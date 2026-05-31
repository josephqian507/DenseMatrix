/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

import ProvableComputation.Bench.DenseMatrixBench

/-!
# DenseMatrix kernel benchmark expressions

The runner script generates temporary Lean files that import this module and
time `#reduce` of the closed definitions below. These are deliberately small:
they measure Lean checking/reduction behavior, not compiled runtime.

`DenseMatrix.transpose` and `DenseMatrix.mul` are covered by the compiler
benchmark runner. Their proof-heavy recursive definitions are not included in
the default kernel `#reduce` suite because they exceed Lean's practical
reduction depth even on tiny closed inputs.
-/

namespace DenseMatrixBench.Kernel

open DenseMatrixBench

/-
Kernel benchmarks reduce small closed expressions.  The suite deliberately uses
the same checksum kernels as the compiled runner so any reduction-time anomaly
still points back to a real DenseMatrix operation rather than to a synthetic
term built only for `#reduce`.
-/
def suiteFor (n : Nat) : Nat :=
  let acc := mixNat 0 (runOfNat n)
  let acc := mixNat acc (runOfMatrixNat n)
  let acc := mixNat acc (runToMatrixNat n)
  let acc := mixNat acc (runGetCheckedNat n)
  let acc := mixNat acc (runGetUncheckedNat n)
  let acc := mixNat acc (runSetCheckedNat n)
  let acc := mixNat acc (runSetUncheckedNat n)
  let acc := mixNat acc (runAddInt n)
  let acc := mixNat acc (runSmulInt n)
  let acc := mixNat acc (runToStringNat n)
  mixNat acc (runAddRat n)

/-
Named kernels let the shell-side runner generate focused temporary files.  That
keeps a slow category, such as access/update or arithmetic, from hiding the rest
of the kernel-reduction signal.
-/
def construction2 : Nat :=
  runOfNat 2

def conversion2 : Nat :=
  mixNat (runOfMatrixNat 2) (runToMatrixNat 2)

def accessAndUpdate2 : Nat :=
  mixNat (mixNat (runGetCheckedNat 2) (runGetUncheckedNat 2))
    (mixNat (runSetCheckedNat 2) (runSetUncheckedNat 2))

def arithmetic2 : Nat :=
  mixNat (mixNat (runAddInt 2) (runSmulInt 2)) (runAddRat 2)

def formatting2 : Nat :=
  runToStringNat 2

def dataProfiles2 : Nat :=
  let acc := mixNat 0 (runAddIntZero 2)
  let acc := mixNat acc (runAddIntBig 2)
  mixNat acc (runAddRatBig 2)

def suite2 : Nat :=
  suiteFor 2

def suite3 : Nat :=
  suiteFor 3

def suite4 : Nat :=
  suiteFor 4

end DenseMatrixBench.Kernel
