#!/usr/bin/env python3
"""Run the fixed DenseMatrix benchmark suite and write reproducible local artifacts."""

from __future__ import annotations

import argparse
import csv
import hashlib
import html
import json
import math
import platform
import shlex
import shutil
import statistics
import subprocess
import sys
import time
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_OUTPUT = Path("/tmp/densematrix-bench")
SAMPLE_KEYS = [
    "suite",
    "operation",
    "variant",
    "implementation",
    "coefficient",
    "pattern",
    "rows",
    "inner",
    "cols",
]
CHECKSUM_KEYS = [
    "suite",
    "operation",
    "coefficient",
    "pattern",
    "rows",
    "inner",
    "cols",
    "process_run",
    "sample",
]
SUMMARY_FIELDS = SAMPLE_KEYS + [
    "sample_count",
    "median_ns",
    "p25_ns",
    "p75_ns",
    "min_ns",
    "max_ns",
    "median_heartbeats",
    "matrix_over_dense",
    "dense_api_over_native",
    "dense_api_over_native_linear_headroom",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("smoke", "full"), default="full")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--overwrite", action="store_true", help="replace a nonempty output directory")
    parser.add_argument("--plots", action="store_true", help="render PNG figures with matplotlib or macOS sips")
    return parser.parse_args()


def run_command(command: list[str], cwd: Path, timeout: float | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def command_text(command: list[str]) -> str:
    return shlex.join(command)


def checked_output(command: list[str], cwd: Path) -> str:
    completed = run_command(command, cwd)
    if completed.returncode:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {command_text(command)}\n{completed.stderr}"
        )
    return completed.stdout.strip()


def cpu_model() -> str:
    if sys.platform == "darwin":
        for key in ("machdep.cpu.brand_string", "hw.model"):
            completed = run_command(["sysctl", "-n", key], Path.cwd())
            if completed.returncode == 0 and completed.stdout.strip():
                return completed.stdout.strip()
    if Path("/proc/cpuinfo").exists():
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.lower().startswith("model name"):
                return line.split(":", 1)[1].strip()
    return platform.processor() or "unknown"


def source_metadata(root: Path) -> dict[str, str]:
    status = checked_output(["git", "status", "--short", "--untracked-files=all"], root)
    if status:
        raise RuntimeError(f"refusing to benchmark a dirty source tree:\n{status}")
    commit = checked_output(["git", "rev-parse", "HEAD"], root)
    return {
        "commit": commit,
        "tree": checked_output(["git", "rev-parse", "HEAD^{tree}"], root),
        "benchmark_sha256": hashlib.sha256(
            (root / "ProvableComputation/Bench/DenseMatrixBench.lean").read_bytes()
        ).hexdigest(),
        "runner_sha256": hashlib.sha256((root / "scripts/run_densematrix_bench.py").read_bytes()).hexdigest(),
        "lean_version": checked_output(["lake", "env", "lean", "--version"], root),
        "uname": checked_output(["uname", "-a"], root),
    }


def prepare_output(output: Path, overwrite: bool) -> None:
    if output.exists():
        if not output.is_dir():
            raise RuntimeError(f"output is not a directory: {output}")
        if any(output.iterdir()):
            if not overwrite:
                raise RuntimeError(f"output is nonempty (pass --overwrite to replace it): {output}")
            shutil.rmtree(output)
    output.mkdir(parents=True, exist_ok=True)


def write_environment(output: Path, metadata: dict[str, str], args: argparse.Namespace) -> None:
    lines = [
        f"date_utc={datetime.now(timezone.utc).isoformat()}",
        f"git_commit={metadata['commit']}",
        f"git_tree={metadata['tree']}",
        f"benchmark_sha256={metadata['benchmark_sha256']}",
        f"runner_sha256={metadata['runner_sha256']}",
        "git_status_short=(clean)",
        f"lean_version={metadata['lean_version']}",
        f"uname={metadata['uname']}",
        f"cpu_model={cpu_model()}",
        f"python={sys.version.splitlines()[0]}",
        f"command_line={shlex.join(sys.argv)}",
        f"profile={args.profile}",
        f"seed={args.seed}",
        "summary_time_unit=ns per logical kernel invocation (raw sample nanos divided by batch)",
        "heartbeats_note=Lean small-object allocation proxy, not bytes or CPU instructions",
        "native_linear_note=unique/linear diagnostic only; it is not public API performance",
    ]
    (output / "environment.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_jsonl(stdout: str, source: str) -> list[dict[str, Any]]:
    samples: list[dict[str, Any]] = []
    for line_number, line in enumerate(stdout.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            sample = json.loads(line)
        except json.JSONDecodeError as error:
            raise RuntimeError(f"non-JSON stdout from {source}, line {line_number}: {line!r}") from error
        missing = [key for key in (*SAMPLE_KEYS, "batch", "nanos", "heartbeats", "checksum") if key not in sample]
        if missing:
            raise RuntimeError(f"missing JSON keys from {source}: {missing}")
        if sample["variant"] not in {
            "dense_api",
            "dense_native",
            "dense_native_linear",
            "matrix_api",
            "control",
        }:
            raise RuntimeError(f"unexpected variant from {source}: {sample['variant']}")
        samples.append(sample)
    if not samples:
        raise RuntimeError(f"no JSONL samples from {source}")
    return samples


def validate_comparable_checksums(samples: list[dict[str, Any]], source: str) -> int:
    grouped: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
    for sample in samples:
        grouped[tuple(sample[field] for field in CHECKSUM_KEYS)].append(sample)
    checked = 0
    for key, group in grouped.items():
        if len(group) < 2:
            continue
        checksums = {int(sample["checksum"]) for sample in group}
        if len(checksums) != 1:
            variants = ", ".join(
                f"{sample['variant']}/{sample['implementation']}={sample['checksum']}" for sample in group
            )
            fields = ", ".join(f"{name}={value}" for name, value in zip(CHECKSUM_KEYS, key, strict=True))
            raise RuntimeError(f"checksum mismatch in {source}: {fields}; {variants}")
        checked += 1
    return checked


def run_benchmark_process(
    root: Path, profile: str, seed: int, process_run: int
) -> tuple[list[dict[str, Any]], str, int]:
    command = [
        "lake",
        "exe",
        "densematrix_bench",
        "--profile",
        profile,
        "--seed",
        str(seed),
        "--process-run",
        str(process_run),
        "--jsonl",
    ]
    completed = run_command(command, root)
    if completed.returncode:
        raise RuntimeError(
            f"benchmark process {process_run} failed ({completed.returncode})\n"
            f"command: {command_text(command)}\n{completed.stderr}"
        )
    samples = parse_jsonl(completed.stdout, f"process {process_run}")
    for sample in samples:
        if sample["process_run"] != process_run:
            raise RuntimeError(f"process_run mismatch in process {process_run}: {sample}")
    return samples, completed.stderr, validate_comparable_checksums(samples, f"process {process_run}")


def percentile(values: list[float], fraction: float) -> float:
    if not values:
        raise ValueError("percentile of empty list")
    ordered = sorted(values)
    position = (len(ordered) - 1) * fraction
    low = int(position)
    high = min(low + 1, len(ordered) - 1)
    return ordered[low] + (ordered[high] - ordered[low]) * (position - low)


def key_of(sample: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(sample[field] for field in SAMPLE_KEYS)


def comparison_key(row: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(row[field] for field in SAMPLE_KEYS if field not in {"variant", "implementation"})


def normalized_ns(sample: dict[str, Any]) -> float:
    batch = int(sample["batch"])
    if batch < 1:
        raise RuntimeError(f"invalid batch: {sample}")
    return float(sample["nanos"]) / batch


def normalized_heartbeats(sample: dict[str, Any]) -> float:
    return float(sample["heartbeats"]) / int(sample["batch"])


def primary_dense(row: dict[str, Any]) -> bool:
    if row["variant"] != "dense_api":
        return False
    if row["operation"] == "scan":
        return row["implementation"] == "dense_checked"
    if row["operation"] == "dot":
        return row["implementation"] == "dense_recursive"
    return row["implementation"] == "dense_api"


def summarize(samples: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
    for sample in samples:
        grouped[key_of(sample)].append(sample)
    rows: list[dict[str, Any]] = []
    for key, group in sorted(grouped.items()):
        durations = [normalized_ns(sample) for sample in group]
        heartbeats = [normalized_heartbeats(sample) for sample in group]
        row = dict(zip(SAMPLE_KEYS, key, strict=True))
        row.update(
            sample_count=len(group),
            median_ns=statistics.median(durations),
            p25_ns=percentile(durations, 0.25),
            p75_ns=percentile(durations, 0.75),
            min_ns=min(durations),
            max_ns=max(durations),
            median_heartbeats=statistics.median(heartbeats),
            matrix_over_dense="",
            dense_api_over_native="",
            dense_api_over_native_linear_headroom="",
        )
        rows.append(row)
    by_compare: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_compare[comparison_key(row)].append(row)
    for group in by_compare.values():
        dense = next((row for row in group if primary_dense(row)), None)
        matrix = next((row for row in group if row["variant"] == "matrix_api"), None)
        native = next((row for row in group if row["variant"] == "dense_native"), None)
        linear = next((row for row in group if row["variant"] == "dense_native_linear"), None)
        if dense and matrix and dense["median_ns"]:
            matrix["matrix_over_dense"] = matrix["median_ns"] / dense["median_ns"]
        if dense and native and native["median_ns"]:
            dense["dense_api_over_native"] = dense["median_ns"] / native["median_ns"]
        if dense and linear and linear["median_ns"]:
            dense["dense_api_over_native_linear_headroom"] = dense["median_ns"] / linear["median_ns"]
    return rows


def format_number(value: Any) -> Any:
    if isinstance(value, float):
        return f"{value:.3f}"
    return value


def write_summary(rows: list[dict[str, Any]], output: Path) -> None:
    with (output / "summary.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=SUMMARY_FIELDS, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: format_number(row[field]) for field in SUMMARY_FIELDS})


def reduce_imports() -> str:
    return "import ProvableComputation.LinearAlgebra.DenseMatrix.Defs\n"


def table_body(size: int, offset: int) -> str:
    entries = []
    for i in range(size):
        for j in range(size):
            value = (i * size + j + offset) % 7 + 1
            entries.append(f"    | {i}, {j} => {value}")
    entries.append("    | _, _ => 0")
    return "\n".join(entries)


def reduce_source(variant: str, operation: str, size: int) -> str:
    dense_a = table_body(size, 1)
    dense_b = table_body(size, 3)
    shared = f"""{reduce_imports()}

def materializeMatrix {{m n : Nat}} {{α : Type}} (M : Matrix (Fin m) (Fin n) α) : Array α :=
  Id.run do
    let mut out : Array α := Array.mkEmpty (m * n)
    let mut i := 0
    while hi : i < m do
      let currentI := i
      have currentILt : currentI < m := by exact hi
      let row : Fin m := ⟨currentI, currentILt⟩
      let mut j := 0
      while hj : j < n do
        let currentJ := j
        have currentJLt : currentJ < n := by exact hj
        let col : Fin n := ⟨currentJ, currentJLt⟩
        out := out.push (M row col)
        j := j + 1
      i := i + 1
    return out
"""
    if variant == "dense":
        definitions = f"""
def denseA : DenseMatrix {size} {size} Nat :=
  DenseMatrix.of fun i j =>
    match i.val, j.val with
{dense_a}

def denseB : DenseMatrix {size} {size} Nat :=
  DenseMatrix.of fun i j =>
    match i.val, j.val with
{dense_b}
"""
        expression = {
            "add": "(DenseMatrix.add denseA denseB).data.toArray",
            "transpose": "(DenseMatrix.transpose denseA).data.toArray",
            "mul": "(DenseMatrix.mul denseA denseB).data.toArray",
        }[operation]
    else:
        definitions = f"""
def matrixA : Matrix (Fin {size}) (Fin {size}) Nat :=
  Matrix.of fun i j =>
    match i.val, j.val with
{dense_a}

def matrixB : Matrix (Fin {size}) (Fin {size}) Nat :=
  Matrix.of fun i j =>
    match i.val, j.val with
{dense_b}
"""
        expression = {
            "add": "materializeMatrix (matrixA + matrixB)",
            "transpose": "materializeMatrix matrixA.transpose",
            "mul": "materializeMatrix (matrixA * matrixB)",
        }[operation]
    return shared + definitions + f"\n#reduce {expression}\n"


def write_reduce_sources(source_dir: Path) -> list[tuple[str, str, int, Path]]:
    source_dir.mkdir(parents=True, exist_ok=True)
    cases: list[tuple[str, str, int, Path]] = []
    for operation in ("add", "transpose", "mul"):
        for size in (2, 3, 4):
            for variant in ("dense", "matrix"):
                path = source_dir / f"{variant}_{operation}_{size}.lean"
                path.write_text(reduce_source(variant, operation, size), encoding="utf-8")
                cases.append((operation, variant, size, path))
    (source_dir / "empty_control.lean").write_text(
        reduce_imports() + "\n-- empty import control\n", encoding="utf-8"
    )
    cases.append(("empty", "control", 0, source_dir / "empty_control.lean"))
    return cases


def run_reductions(root: Path, output: Path, profile: str, validation: list[str]) -> list[dict[str, Any]]:
    repeats = 1 if profile == "smoke" else 5
    timeout_seconds = 120.0
    cases = write_reduce_sources(output / "src")
    control_case = next(case for case in cases if case[0] == "empty")
    measured_cases = [case for case in cases if case[0] != "empty"]
    raw_rows: list[dict[str, Any]] = []

    def measure_case(
        repeat: int,
        case: tuple[str, str, int, Path],
        control_wall_ns: int | None,
    ) -> dict[str, Any]:
        operation, variant, size, source = case
        command = ["lake", "env", "lean", str(source)]
        start = time.perf_counter_ns()
        timed_out = False
        try:
            completed = run_command(command, root, timeout=timeout_seconds)
            exit_code = completed.returncode
            stderr = completed.stderr
        except subprocess.TimeoutExpired as error:
            timed_out = True
            exit_code = -1
            stderr = str(error)
        wall_ns = time.perf_counter_ns() - start
        if timed_out or exit_code != 0:
            validation.append(
                f"reduce FAIL operation={operation} variant={variant} size={size} repeat={repeat}: {stderr}"
            )
            raise RuntimeError(validation[-1])
        paired_control = wall_ns if control_wall_ns is None else control_wall_ns
        return {
            "measurement": "exploratory kernel-reduction measurement",
            "profile": profile,
            "operation": operation,
            "variant": variant,
            "size": size,
            "repeat": repeat,
            "wall_ns": wall_ns,
            "control_wall_ns": paired_control,
            "net_wall_ns": wall_ns - paired_control,
            "exit_code": exit_code,
            "timeout": str(timed_out).lower(),
        }

    for repeat in range(repeats):
        control_row = measure_case(repeat, control_case, None)
        raw_rows.append(control_row)
        control_wall_ns = int(control_row["wall_ns"])
        for case in measured_cases:
            raw_rows.append(measure_case(repeat, case, control_wall_ns))
    raw_fields = [
        "measurement",
        "profile",
        "operation",
        "variant",
        "size",
        "repeat",
        "wall_ns",
        "control_wall_ns",
        "net_wall_ns",
        "exit_code",
        "timeout",
    ]
    with (output / "raw.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=raw_fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(raw_rows)
    grouped: dict[tuple[str, str, int], list[int]] = defaultdict(list)
    for row in raw_rows:
        grouped[(row["operation"], row["variant"], row["size"])].append(int(row["wall_ns"]))
    summary: list[dict[str, Any]] = []
    grouped_rows: dict[tuple[str, str, int], list[dict[str, Any]]] = defaultdict(list)
    for row in raw_rows:
        grouped_rows[(str(row["operation"]), str(row["variant"]), int(row["size"]))].append(row)
    for (operation, variant, size), values in sorted(grouped.items()):
        rows = grouped_rows[(operation, variant, size)]
        net_values = [int(row["net_wall_ns"]) for row in rows]
        control_values = [int(row["control_wall_ns"]) for row in rows]
        summary.append(
            {
                "measurement": "exploratory kernel-reduction measurement",
                "interpretation": "control" if operation == "empty" else "inconclusive",
                "operation": operation,
                "variant": variant,
                "size": size,
                "sample_count": len(values),
                "raw_median_ns": statistics.median(values),
                "raw_p25_ns": percentile([float(value) for value in values], 0.25),
                "raw_p75_ns": percentile([float(value) for value in values], 0.75),
                "raw_min_ns": min(values),
                "raw_max_ns": max(values),
                "control_median_ns": statistics.median(control_values),
                "net_median_ns": statistics.median(net_values),
                "net_p25_ns": percentile([float(value) for value in net_values], 0.25),
                "net_p75_ns": percentile([float(value) for value in net_values], 0.75),
                "net_min_ns": min(net_values),
                "net_max_ns": max(net_values),
            }
        )
    fields = [
        "measurement",
        "interpretation",
        "operation",
        "variant",
        "size",
        "sample_count",
        "raw_median_ns",
        "raw_p25_ns",
        "raw_p75_ns",
        "raw_min_ns",
        "raw_max_ns",
        "control_median_ns",
        "net_median_ns",
        "net_p25_ns",
        "net_p75_ns",
        "net_min_ns",
        "net_max_ns",
    ]
    with (output / "summary.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for row in summary:
            writer.writerow({field: format_number(row[field]) for field in fields})
    validation.append(
        "reduce PASS: "
        f"{len(raw_rows)} independent Lean processes; same-repeat control-adjusted "
        "Lean-process time is exploratory/inconclusive"
    )
    return summary


def run_ir_check(root: Path, output: Path, validation: list[str]) -> str:
    source = output / "ir-check.lean"
    source.write_text(
        """import ProvableComputation.LinearAlgebra.DenseMatrix.Defs

set_option trace.compiler.ir.result true

@[noinline]
def inspectLinearScale (input : Array Rat) : Array Rat :=
  Id.run do
    let mut out := input
    let base := 64
    for j in [0:64] do
      out := out.set! (base + j) (2 * out[base + j]!)
    return out

@[noinline]
def inspectLinearReplace (input : Array Rat) : Array Rat :=
  Id.run do
    let mut out := input
    let sourceBase := 0
    let targetBase := 63 * 64
    for j in [0:64] do
      out := out.set! (targetBase + j) (out[targetBase + j]! + 3 * out[sourceBase + j]!)
    return out

@[noinline]
def inspectNativeMultiply (left right : Array Nat) : Array Nat :=
  Id.run do
    let mut out := Array.mkEmpty 64
    for i in [0:8] do
      let rowBase := i * 8
      for j in [0:8] do
        let mut sum := 0
        for k in [0:8] do
          sum := sum + left[rowBase + k]! * right[k * 8 + j]!
        out := out.push sum
    return out
""",
        encoding="utf-8",
    )
    completed = run_command(["lake", "env", "lean", str(source)], root)
    trace = completed.stdout + completed.stderr
    (output / "ir-check.txt").write_text(trace, encoding="utf-8")
    if completed.returncode:
        raise RuntimeError(f"IR check failed: {completed.stderr}")
    has_shared = "isShared" in trace
    has_set = "Array.set" in trace or "set!" in trace
    has_push = "Array.push" in trace or "push" in trace
    if has_shared and has_set:
        conclusion = "unique-reference fast path appears available; not demonstrated for every update"
    else:
        conclusion = "unique-reference fast path not demonstrated by this IR check"
    (output / "ir-check-summary.txt").write_text(
        "\n".join(
            [
                conclusion,
                f"contains_isShared={has_shared}",
                f"contains_array_set={has_set}",
                f"contains_array_push={has_push}",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    validation.append(f"IR PASS: {conclusion}")
    return conclusion


def label(row: dict[str, Any]) -> str:
    name = str(row["variant"])
    implementation = str(row.get("implementation", ""))
    if name == "dense_native_linear":
        return "dense_native_linear (unique/linear diagnostic)"
    if implementation and implementation != name:
        return f"{name}/{implementation}"
    return name


def finite(value: Any) -> float:
    return float(value)


PLOT_COLORS = ("#145A8D", "#B56E00", "#5C7F2B", "#9A4F6E", "#5B5F97")


def format_duration(value: float) -> str:
    absolute = abs(value)
    if absolute >= 1_000_000:
        return f"{value / 1_000_000:.2f}".rstrip("0").rstrip(".") + " ms"
    if absolute >= 1_000:
        return f"{value / 1_000:.2f}".rstrip("0").rstrip(".") + " µs"
    return f"{value:.0f} ns"


def ordered_categories(rows: list[dict[str, Any]], field: str, order: list[str] | None) -> list[str]:
    present = {str(row[field]) for row in rows}
    ordered = [value for value in order or [] if value in present]
    return ordered + sorted(present - set(ordered))


def grouped_series(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    series: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        series[label(row)].append(row)
    return series


def panel_bounds(rows: list[dict[str, Any]], allow_negative: bool) -> tuple[float, float]:
    lower = min(finite(row["p25_ns"]) for row in rows)
    upper = max(finite(row["p75_ns"]) for row in rows)
    minimum = min(0.0, lower) if allow_negative else 0.0
    if upper <= minimum:
        upper = minimum + 1.0
    padding = (upper - minimum) * 0.08
    return minimum - (padding if allow_negative else 0.0), upper + padding


def draw_panels_matplotlib(
    plt: Any,
    output: Path,
    filename: str,
    title: str,
    panels: list[tuple[str, list[dict[str, Any]], str]],
    *,
    x_label: str,
    numeric_x: bool,
    log_x: bool,
    category_order: list[str] | None,
    allow_negative: bool,
    subtitle: str,
    connect_lines: bool,
) -> None:
    figure, axes = plt.subplots(
        len(panels), 1, figsize=(12, max(3.8, 3.4 * len(panels))), squeeze=False
    )
    for axis, (panel_title, rows, x_field) in zip(axes[:, 0], panels, strict=True):
        series = grouped_series(rows)
        if numeric_x:
            x_ticks = sorted({finite(row[x_field]) for row in rows})
            x_labels = [str(int(value)) if value.is_integer() else str(value) for value in x_ticks]
        else:
            x_labels = ordered_categories(rows, x_field, category_order)
            x_index = {value: index for index, value in enumerate(x_labels)}
        for color, (series_label, values) in zip(PLOT_COLORS, sorted(series.items()), strict=False):
            if numeric_x:
                values.sort(key=lambda row: finite(row[x_field]))
                x_values = [finite(row[x_field]) for row in values]
            else:
                values.sort(key=lambda row: x_index[str(row[x_field])])
                x_values = [x_index[str(row[x_field])] for row in values]
            y_values = [finite(row["median_ns"]) for row in values]
            lower = [max(0.0, value - finite(row["p25_ns"])) for value, row in zip(y_values, values, strict=True)]
            upper = [max(0.0, finite(row["p75_ns"]) - value) for value, row in zip(y_values, values, strict=True)]
            axis.errorbar(
                x_values,
                y_values,
                yerr=[lower, upper],
                marker="o",
                capsize=3,
                color=color,
                label=series_label,
                linestyle="-" if connect_lines else "none",
            )
        if numeric_x:
            axis.set_xticks(x_ticks, x_labels)
            if log_x:
                axis.set_xscale("log", base=2)
        else:
            axis.set_xticks(range(len(x_labels)), x_labels, rotation=25, ha="right")
        minimum, maximum = panel_bounds(rows, allow_negative)
        axis.set_ylim(minimum, maximum)
        if allow_negative:
            axis.axhline(0, color="#495057", linewidth=0.8)
        axis.set_title(panel_title)
        axis.set_xlabel(x_label)
        axis.set_ylabel("median time (ns)")
        axis.grid(axis="y", alpha=0.25)
        axis.legend(fontsize=8, loc="best")
    figure.suptitle(title, y=0.995)
    figure.text(0.5, 0.968, subtitle, ha="center", va="top", fontsize=9, color="#495057")
    figure.tight_layout(rect=(0, 0, 1, 0.95))
    figure.savefig(output / filename, dpi=160)
    plt.close(figure)


def svg_text(
    lines: list[str],
    x: float,
    y: float,
    value: str,
    *,
    size: int = 16,
    anchor: str = "start",
    fill: str = "#212529",
    transform: str = "",
) -> None:
    transform_attribute = f' transform="{transform}"' if transform else ""
    lines.append(
        f'<text x="{x:.1f}" y="{y:.1f}" font-family="Helvetica,Arial,sans-serif" '
        f'font-size="{size}" text-anchor="{anchor}" fill="{fill}"{transform_attribute}>'
        f"{html.escape(value)}</text>"
    )


def draw_panels_svg(
    output: Path,
    filename: str,
    title: str,
    panels: list[tuple[str, list[dict[str, Any]], str]],
    *,
    x_label: str,
    numeric_x: bool,
    log_x: bool,
    category_order: list[str] | None,
    allow_negative: bool,
    subtitle: str,
    connect_lines: bool,
) -> None:
    if shutil.which("sips") is None:
        raise RuntimeError("plots require matplotlib or the macOS sips SVG converter")
    width = 1800
    header = 82
    panel_height = 390
    height = header + panel_height * len(panels)
    left, right, legend_left = 125.0, 1245.0, 1305.0
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        f'<rect width="{width}" height="{height}" fill="#ffffff"/>',
    ]
    svg_text(lines, width / 2, 32, title, size=24, anchor="middle")
    svg_text(lines, width / 2, 58, subtitle, size=14, anchor="middle", fill="#495057")
    for panel_index, (panel_title, rows, x_field) in enumerate(panels):
        top = header + panel_index * panel_height + 28.0
        bottom = top + 238.0
        svg_text(lines, left, top - 10, panel_title, size=18)
        lines.append(
            f'<rect x="{left:.1f}" y="{top:.1f}" width="{right - left:.1f}" height="{bottom - top:.1f}" '
            'fill="#ffffff" stroke="#adb5bd" stroke-width="1"/>'
        )
        minimum, maximum = panel_bounds(rows, allow_negative)

        def y_coord(value: float) -> float:
            return bottom - (value - minimum) / (maximum - minimum) * (bottom - top)

        for tick in range(5):
            value = minimum + (maximum - minimum) * tick / 4
            y = y_coord(value)
            lines.append(
                f'<line x1="{left:.1f}" y1="{y:.1f}" x2="{right:.1f}" y2="{y:.1f}" '
                'stroke="#dee2e6" stroke-width="1"/>'
            )
            svg_text(lines, left - 12, y + 5, format_duration(value), size=12, anchor="end", fill="#495057")
        if allow_negative and minimum < 0 < maximum:
            y_zero = y_coord(0)
            lines.append(
                f'<line x1="{left:.1f}" y1="{y_zero:.1f}" x2="{right:.1f}" y2="{y_zero:.1f}" '
                'stroke="#495057" stroke-width="1.2"/>'
            )

        if numeric_x:
            x_values = sorted({finite(row[x_field]) for row in rows})
            transformed = [math.log2(value) if log_x else value for value in x_values]
            x_min, x_max = min(transformed), max(transformed)
            if x_min == x_max:
                x_max = x_min + 1.0

            def x_coord(value: float) -> float:
                mapped = math.log2(value) if log_x else value
                return left + (mapped - x_min) / (x_max - x_min) * (right - left)

            for value in x_values:
                x = x_coord(value)
                lines.append(
                    f'<line x1="{x:.1f}" y1="{bottom:.1f}" x2="{x:.1f}" y2="{bottom + 5:.1f}" '
                    'stroke="#495057" stroke-width="1"/>'
                )
                svg_text(
                    lines,
                    x,
                    bottom + 23,
                    str(int(value)) if value.is_integer() else str(value),
                    size=12,
                    anchor="middle",
                    fill="#495057",
                )
        else:
            categories = ordered_categories(rows, x_field, category_order)
            category_index = {value: index for index, value in enumerate(categories)}
            spacing = (right - left) / max(len(categories) - 1, 1)

            def x_coord(value: float) -> float:
                return left + value * spacing

            for category, index in category_index.items():
                x = x_coord(float(index))
                lines.append(
                    f'<line x1="{x:.1f}" y1="{bottom:.1f}" x2="{x:.1f}" y2="{bottom + 5:.1f}" '
                    'stroke="#495057" stroke-width="1"/>'
                )
                svg_text(
                    lines,
                    x,
                    bottom + 26,
                    category,
                    size=11,
                    anchor="end",
                    fill="#495057",
                    transform=f"rotate(-28 {x:.1f} {bottom + 26:.1f})",
                )

        for color, (series_label, values) in zip(PLOT_COLORS, sorted(grouped_series(rows).items()), strict=False):
            if numeric_x:
                values.sort(key=lambda row: finite(row[x_field]))
                x_values_for_series = [finite(row[x_field]) for row in values]
            else:
                values.sort(key=lambda row: category_index[str(row[x_field])])
                x_values_for_series = [float(category_index[str(row[x_field])]) for row in values]
            points = [
                (x_coord(x), y_coord(finite(row["median_ns"])))
                for x, row in zip(x_values_for_series, values, strict=True)
            ]
            if connect_lines and len(points) > 1:
                point_text = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
                lines.append(f'<polyline points="{point_text}" fill="none" stroke="{color}" stroke-width="2.5"/>')
            for (x, y), row in zip(points, values, strict=True):
                low = y_coord(finite(row["p25_ns"]))
                high = y_coord(finite(row["p75_ns"]))
                lines.append(
                    f'<line x1="{x:.1f}" y1="{low:.1f}" x2="{x:.1f}" y2="{high:.1f}" '
                    f'stroke="{color}" stroke-width="1.5"/>'
                )
                lines.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="4.2" fill="{color}"/>')
            legend_y = top + 20 + sorted(grouped_series(rows)).index(series_label) * 24
            if connect_lines:
                lines.append(
                    f'<line x1="{legend_left:.1f}" y1="{legend_y:.1f}" x2="{legend_left + 24:.1f}" '
                    f'y2="{legend_y:.1f}" stroke="{color}" stroke-width="2.5"/>'
                )
            else:
                lines.append(f'<circle cx="{legend_left + 12:.1f}" cy="{legend_y:.1f}" r="4.2" fill="{color}"/>')
            svg_text(lines, legend_left + 32, legend_y + 5, series_label, size=12)
        svg_text(lines, (left + right) / 2, bottom + 67, x_label, size=13, anchor="middle", fill="#495057")
        svg_text(lines, left - 82, (top + bottom) / 2, "median time", size=13, anchor="middle", fill="#495057",
                 transform=f"rotate(-90 {left - 82:.1f} {(top + bottom) / 2:.1f})")
    lines.append("</svg>")
    svg_path = output / Path(filename).with_suffix(".svg")
    png_path = output / filename
    svg_path.write_text("\n".join(lines) + "\n")
    converted = run_command(["sips", "-s", "format", "png", str(svg_path), "--out", str(png_path)], output)
    if converted.returncode:
        raise RuntimeError(f"sips failed for {filename}: {converted.stderr}")
    svg_path.unlink()


def draw_panels(
    output: Path,
    filename: str,
    title: str,
    panels: list[tuple[str, list[dict[str, Any]], str]],
    *,
    x_label: str,
    numeric_x: bool = False,
    log_x: bool = False,
    category_order: list[str] | None = None,
    allow_negative: bool = False,
    subtitle: str = "Median time per logical invocation; error bars show IQR.",
    connect_lines: bool = True,
) -> str:
    if not panels:
        return "none"
    try:
        import matplotlib.pyplot as plt  # type: ignore[import-not-found]
    except ImportError:
        draw_panels_svg(
            output, filename, title, panels, x_label=x_label, numeric_x=numeric_x, log_x=log_x,
            category_order=category_order, allow_negative=allow_negative, subtitle=subtitle,
            connect_lines=connect_lines,
        )
        return "svg+sips"
    draw_panels_matplotlib(
        plt, output, filename, title, panels, x_label=x_label, numeric_x=numeric_x, log_x=log_x,
        category_order=category_order, allow_negative=allow_negative, subtitle=subtitle,
        connect_lines=connect_lines,
    )
    return "matplotlib"


def row_shape(row: dict[str, Any]) -> str:
    if int(row["inner"]) > 0:
        return f"{row['rows']}×{row['inner']}×{row['cols']}"
    return f"{row['rows']}×{row['cols']}"


def make_plots(summary: list[dict[str, Any]], reduce_summary: list[dict[str, Any]], output: Path) -> str:
    renderers: set[str] = set()

    def draw(*args: Any, **kwargs: Any) -> None:
        renderer = draw_panels(*args, **kwargs)
        if renderer != "none":
            renderers.add(renderer)

    construction_order = ["64×64", "256×64", "64×256", "256×256", "512×128", "128×512"]
    elementwise_order = ["64×64", "128×128", "256×256", "64×1024", "1024×64"]
    mul_order = [
        "8×8×8", "16×16×16", "24×24×24", "32×32×32", "40×40×40", "8×256×8",
        "64×16×64", "16×128×64", "64×128×16", "32×512×8", "8×512×32",
    ]
    pivot_order = ["128×128", "512×64", "64×512", "512×512"]
    rref_order = [
        "dense_full_rank 6×6", "dense_full_rank 10×10", "dense_full_rank 14×14",
        "swap_heavy 6×6", "swap_heavy 10×10", "swap_heavy 14×14",
        "rank_deficient 6×6", "rank_deficient 10×10", "rank_deficient 14×14",
        "sparse_late_pivot 24×8", "sparse_late_pivot 8×24", "already_echelon 14×14",
    ]
    elementwise = [row for row in summary if row["suite"] == "elementwise"]
    draw(
        output,
        "01_elementwise_api.png",
        "DenseMatrix elementwise API and materialized Matrix comparison",
        [
            (operation, [row | {"shape": row_shape(row)} for row in elementwise if row["operation"] == operation], "shape")
            for operation in ("add", "smul", "transpose")
            if any(row["operation"] == operation for row in elementwise)
        ],
        x_label="matrix shape", category_order=elementwise_order,
    )
    dot_rows = [row for row in summary if row["suite"] == "dot"]
    draw(
        output, "02_dot_kernels.png", "Dot-product kernels", [("dot", dot_rows, "inner")],
        x_label="inner dimension", numeric_x=True, log_x=True,
    )
    mul_rows = [row | {"shape": row_shape(row)} for row in summary if row["suite"] == "mul"]
    draw(
        output,
        "03_mul_api_and_native.png",
        "Matrix multiplication: square and rectangular cases",
        [
            ("square cases", [row for row in mul_rows if row["rows"] == row["inner"] == row["cols"]], "shape"),
            ("rectangular cases", [row for row in mul_rows if not (row["rows"] == row["inner"] == row["cols"])], "shape"),
        ],
        x_label="m×k×n", category_order=mul_order, connect_lines=False,
        subtitle="Independent workloads; points are intentionally not connected. Error bars show IQR.",
    )
    row_rows = [row for row in summary if row["suite"] == "row_ops"]
    for filename, pattern, title in (
        ("04_row_ops_rows_scaling.png", "rows_fixed_cols_64", "Row operations: time vs rows (64 columns)"),
        ("05_row_ops_cols_scaling.png", "cols_fixed_rows_64", "Row operations: time vs columns (64 rows)"),
    ):
        selected_rows = [row | {"scale": row["rows"] if pattern.startswith("rows") else row["cols"]}
                         for row in row_rows if row["pattern"] == pattern]
        draw(
            output,
            filename,
            title,
            [
                (operation, [row for row in selected_rows if row["operation"] == operation], "scale")
                for operation in ("swap_row", "scale_row", "replace_row")
                if any(row["operation"] == operation for row in selected_rows)
            ],
            x_label="rows" if pattern.startswith("rows") else "columns", numeric_x=True, log_x=True,
        )
    pivot_rows = [row | {"shape": row_shape(row)} for row in summary if row["suite"] == "pivot"]
    draw(
        output,
        "06_pivot_patterns.png",
        "Pivot-search patterns",
        [
            (shape, [row for row in pivot_rows if row["shape"] == shape], "pattern")
            for shape in pivot_order
            if any(row["shape"] == shape for row in pivot_rows)
        ],
        x_label="pivot pattern", category_order=["first_entry", "late_row", "late_column", "last_entry", "none"],
    )
    rref_rows = [row | {"case": f"{row['pattern']} {row_shape(row)}"} for row in summary if row["suite"] == "rref"]
    draw(
        output,
        "07_ref_rref_patterns.png",
        "Raw REF/RREF patterns (full-rank cases isolated)",
        [
            (f"{operation}: dense_full_rank", [
                row for row in rref_rows
                if row["operation"] == operation and row["pattern"] == "dense_full_rank"
            ], "case")
            for operation in ("ref", "rref")
            if any(row["operation"] == operation for row in rref_rows)
        ] + [
            (f"{operation}: other patterns", [
                row for row in rref_rows
                if row["operation"] == operation and row["pattern"] != "dense_full_rank"
            ], "case")
            for operation in ("ref", "rref")
            if any(row["operation"] == operation for row in rref_rows)
        ],
        x_label="pattern and shape", category_order=rref_order,
        subtitle="Full-rank cases are isolated so the remaining patterns stay readable; error bars show IQR.",
        connect_lines=False,
    )
    conversion_rows = [row | {"shape": row_shape(row)} for row in summary if row["suite"] == "construction"]
    draw(
        output,
        "08_conversion_cost.png",
        "Construction and conversion costs",
        [
            (operation, [row for row in conversion_rows if row["operation"] == operation], "shape")
            for operation in ("construct", "of_matrix", "to_matrix_materialize")
            if any(row["operation"] == operation for row in conversion_rows)
        ],
        x_label="matrix shape", category_order=construction_order,
    )
    reduce_rows = [
        row
        | {
            "median_ns": row["net_median_ns"],
            "p25_ns": row["net_p25_ns"],
            "p75_ns": row["net_p75_ns"],
        }
        for row in reduce_summary
        if row["operation"] != "empty"
    ]
    draw(
        output,
        "09_reduce_exploratory.png",
        "Exploratory #reduce: same-repeat control-adjusted process wall time (inconclusive)",
        [
            (operation, [row for row in reduce_rows if row["operation"] == operation], "size")
            for operation in ("add", "transpose", "mul")
            if any(row["operation"] == operation for row in reduce_rows)
        ],
        x_label="square size", numeric_x=True, allow_negative=True,
        subtitle="Case process wall time minus the one empty-control process from the same repeat; bars show IQR.",
    )
    return ", ".join(sorted(renderers))


def write_results_readme(output: Path, metadata: dict[str, str], args: argparse.Namespace) -> None:
    plots = "Nine PNG figures are included." if args.plots else "PNG figures were not requested."
    (output / "README.md").write_text(
        f"""# DenseMatrix benchmark results — `{metadata['commit'][:7]}`

This directory was generated from a clean source tree by
`scripts/run_densematrix_bench.py`.

- Subject revision: `{metadata['commit']}`
- Subject tree: `{metadata['tree']}`
- Benchmark source SHA-256: `{metadata['benchmark_sha256']}`
- Runner SHA-256: `{metadata['runner_sha256']}`
- Profile: `{args.profile}`

- `compiled/` contains the compiled benchmark samples and summary.
- `diagnostics/` contains the environment, build logs, validation, and compiler-IR record.
- `reduce/` contains exploratory `#reduce` inputs and summaries.
- `figures/` is optional. {plots}

Timing values vary by machine and load. Reproducibility means the recorded source and
protocol revisions, case identities, checksums, and derived summaries can be regenerated;
it does not require equal nanosecond measurements across machines.

Generate a new snapshot from a clean checkout into an empty directory:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/run_densematrix_bench.py \\
  --profile {args.profile} \\
  --output /path/to/empty-results-directory
```

Pass `--plots` only where matplotlib or macOS `sips` is available. Pass `--overwrite`
only to intentionally replace an existing output directory.
""",
        encoding="utf-8",
    )


def main() -> int:
    args = parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output.resolve()
    metadata = source_metadata(root)
    prepare_output(output, args.overwrite)
    compiled = output / "compiled"
    diagnostics = output / "diagnostics"
    reduce = output / "reduce"
    for directory in (compiled, diagnostics, reduce):
        directory.mkdir()
    validation: list[str] = []
    write_environment(diagnostics, metadata, args)
    build = run_command(["lake", "build", "densematrix_bench"], root)
    (diagnostics / "build.stdout.txt").write_text(build.stdout, encoding="utf-8")
    (diagnostics / "build.stderr.txt").write_text(build.stderr, encoding="utf-8")
    if build.returncode:
        raise RuntimeError(f"build failed:\n{build.stderr}")
    validation.append("build PASS: lake build densematrix_bench")
    smoke, smoke_stderr, smoke_checksum_groups = run_benchmark_process(root, "smoke", args.seed, 0)
    with (compiled / "smoke.jsonl").open("w", encoding="utf-8") as handle:
        for sample in smoke:
            handle.write(json.dumps(sample, separators=(",", ":")) + "\n")
    validation.append(f"smoke PASS: {len(smoke)} samples")
    validation.append(f"smoke checksum PASS: {smoke_checksum_groups} comparable process/sample cases")
    if smoke_stderr.strip():
        (diagnostics / "smoke-check.stderr.txt").write_text(smoke_stderr, encoding="utf-8")
        validation.append("smoke stderr recorded (Lean build warnings may be baseline warnings)")
    process_count = 1 if args.profile == "smoke" else 3
    raw_samples: list[dict[str, Any]] = []
    for process_run in range(process_count):
        samples, stderr, checksum_groups = run_benchmark_process(root, args.profile, args.seed, process_run)
        raw_samples.extend(samples)
        validation.append(f"{args.profile} process {process_run} PASS: {len(samples)} samples")
        validation.append(
            f"{args.profile} process {process_run} checksum PASS: {checksum_groups} comparable process/sample cases"
        )
        if stderr.strip():
            (diagnostics / f"{args.profile}-process-{process_run}.stderr.txt").write_text(
                stderr, encoding="utf-8"
            )
            validation.append(f"{args.profile} process {process_run} stderr recorded")
    with (compiled / "raw.jsonl").open("w", encoding="utf-8") as handle:
        for sample in raw_samples:
            handle.write(json.dumps(sample, separators=(",", ":")) + "\n")
    summary = summarize(raw_samples)
    write_summary(summary, compiled)
    ir_conclusion = run_ir_check(root, diagnostics, validation)
    reduce_summary = run_reductions(root, reduce, args.profile, validation)
    if args.plots:
        figures = output / "figures"
        figures.mkdir()
        plot_renderer = make_plots(summary, reduce_summary, figures)
        validation.append(f"plots PASS: {plot_renderer}")
    else:
        validation.append("plots SKIPPED: pass --plots when a renderer is available")
    validation.append(f"IR conclusion: {ir_conclusion}")
    (diagnostics / "validation.txt").write_text("\n".join(validation) + "\n", encoding="utf-8")
    write_results_readme(output, metadata, args)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"run_densematrix_bench.py: {error}", file=sys.stderr)
        raise SystemExit(1)
