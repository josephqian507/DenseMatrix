# DenseMatrix Cleanup and Correctness Plan

## Scope and design

The goal is a working, computable implementation of standard dense-matrix
algorithms. `DenseMatrix` owns the vector-backed representation and executable
algorithms; mathlib's function-backed `Matrix` supplies reusable theory. The
current focus is Gaussian elimination, together with basic operations such as
addition and multiplication.

* Work only in `ProvableComputation/LinearAlgebra/DenseMatrix` and, when needed,
  `ProvableComputation/LinearAlgebra/Matrix`. The older function-backed
  Gaussian-elimination directory is reference material; do not modify or remove it.
* Keep executable algorithms and their algorithm-specific invariants in
  `DenseMatrix`. State reusable linear-algebra theory for mathlib `Matrix` rather
  than re-proving it for `DenseMatrix`.
* Before adding Matrix theory, search the pinned mathlib sources and Lean's local
  environment. Reuse an existing theorem whenever possible. Record any genuinely
  reusable theorem that should eventually be proposed upstream.
* `ProvableComputation.LinearAlgebra.Matrix.ElementaryRowOperations` contains an
  unreleased project PR. If a mathlib release includes that work, update the
  dependency and replace project-local imports as appropriate.
* Keep generic Matrix theory independent of the executable DenseMatrix modules.
  An adapter about this particular algorithm may depend on DenseMatrix, but should
  live with the algorithm rather than in generic Matrix theory.

## Conventions

* `A.IsRowEchelonOf B` and `A.IsReducedRowEchelonOf B` are form-first:
  `A` is the row-equivalent echelon-form representative of source `B`.
  Thus the echelon/reduced-echelon field concerns `A`.
* Use mathlib's `Matrix.mulVec` for matrix-vector statements. Do not represent a
  vector as a one-column `DenseMatrix` merely to state a kernel theorem.
* Public theorem names must describe their statements. Prefer names such as
  `rowEchelonForm_rowEquivalent` or
  `reducedRowEchelonForm_mulVec_eq_zero_iff`; avoid vague names such as
  `ref_proof`, `rref_proof`, `steps_helper`, and `mul_by_inv`.
* Avoid scaffold terminology in public names and documentation: in particular,
  do not use `raw`, `stage`, or `semantic goal` when a direct mathematical or
  algorithmic name is available.
* Use `scale` consistently for row scaling. Do not call the corresponding
  `RowOp` constructor `factor`.
* Preserve commented WIP as reference unless a task explicitly authorizes its
  removal. Do not revive it wholesale: port only a deliberately chosen argument,
  update its names and assumptions, and keep it consistent with these conventions.
* Do not disable linters. Address warnings as part of cleanup when touching the
  affected proof; otherwise leave them visible.

## Phase 1: Cleanup prerequisites

Complete these organizational tasks before adding new algorithms or broadening
the API.

1. Correct stale documentation, stale names, and stale references to definitions
   that do not exist, including references to `rawReducedRowEchelonForm`.
2. Rename vague correctness and log theorems to state what they prove. In
   particular, use names based on `rowReductionAux`, `eliminateCol`,
   `rowEchelonForm`, and `reducedRowEchelonForm`.
3. Rename `RowOp.factor` to `RowOp.scale` and update associated documentation.
4. Remove unnecessary DenseMatrix imports from generic Matrix theory. In
   particular, RREF uniqueness theory must not depend on executable RREF code.
5. Keep inactive Matrix definitions that duplicate mathlib inactive; do not create
   competing notions of pivot, echelon form, or row equivalence.
6. Do not paper over the broken canonical-RREF wrapper. Repair it only after the
   guarantees it needs have been proved.

## Phase 2: Certified row reduction

**Status:** Complete. The executable log now proves row equivalence, kernel preservation is
derived from that result, REF/RREF outputs satisfy mathlib's echelon predicates, and the
canonical-RREF adapter is backed by the reduced-row-echelon guarantee.

The `steps` field of `RowReductionResult` is an important computational
certificate. Prove row equivalence directly from that certificate, then derive
kernel preservation as a corollary.

### 2.1 Valid logged operations

* Define a clear predicate for invertible logged operations, for example
  `RowOp.IsInvertible`.
* A swap is invertible; a scale is invertible when its factor is nonzero; and a
  replacement is invertible when its source and target rows differ.
* Prove that every operation emitted by `rowReductionAux` satisfies this predicate.
  In particular, selected pivots are nonzero before normalization, and elimination
  never replaces a row using itself.
* Keep arbitrary non-invertible `RowOp` values representable. The guarantee is
  about algorithm-produced logs, not every value of the datatype.

### 2.2 Replay and row equivalence

* Retain and clean up the theorem that replaying `steps` with `applyRowOp` returns
  the algorithm's matrix output.
* Prove that applying one valid logged operation gives a row-equivalent Matrix
  conversion. Reuse the Matrix-level theorems for swaps, row scaling, and
  transvections.
* Prefer the dedicated Matrix row-scaling construction to encoding a scale as a
  same-row transvection.
* Induct over a valid operation list to prove that replaying it is row-equivalent
  to its input. Combine this with replay correctness to prove:

  ```lean
  Matrix.RowEquivalent M.toMatrix (rowEchelonForm M).matrix.toMatrix
  Matrix.RowEquivalent M.toMatrix (reducedRowEchelonForm M).matrix.toMatrix
  ```

* An explicit product of elementary matrices may be added later as a stronger
  certificate, but it is not required to establish the row-equivalence proposition.

### 2.3 Kernel preservation

* Derive, rather than independently prove, the `mulVec` kernel statements from
  row equivalence using the Matrix-level theorem
  `Matrix.RowEquivalent.mul_eq_zero_iff`.
* The public kernel theorem names should state the algorithm and the `mulVec`
  conclusion, for example `reducedRowEchelonForm_mulVec_eq_zero_iff`.
* Remove the old proof path based on DenseMatrix multiplication by a one-column
  matrix only after its replacement is established. It should not impose
  unnecessary `Inhabited` or `NeZero` assumptions on the semantic theorem.

### 2.4 Echelon-form guarantees

* Prove that the converted output of `rowEchelonForm` is `Matrix.IsRowEchelon`.
* Prove that the converted output of `reducedRowEchelonForm` is
  `Matrix.IsReducedRowEchelon`.
* Build these from explicit algorithm invariants and existing mathlib echelon
  predicates; do not define a project-local competing echelon predicate.
* Combine row equivalence and form proofs into the form-first structures:

  ```lean
  (rowEchelonForm M).matrix.toMatrix.IsRowEchelonOf M.toMatrix
  (reducedRowEchelonForm M).matrix.toMatrix.IsReducedRowEchelonOf M.toMatrix
  ```

### 2.5 Canonical RREF

* Once the reduced-row-echelon guarantee exists, repair the canonical wrapper to
  depend on it.
* Keep semantic RREF uniqueness generic over mathlib `Matrix`; keep the fact that
  a particular executable output is canonical in an algorithm-facing adapter.

## Phase 3: Representation and reuse cleanup

**Status:** Complete. `DenseMatrix.ringEquivMatrix` packages the square algebra bridge, the
ring instance reuses the established semiring laws, executable function construction no longer
routes through `ofMatrix`, and rectangular bridge theorems remain available.

After the existing guarantees are complete, improve the implementation without
adding unrelated algorithms.

* Provide an appropriate square-matrix algebra equivalence between DenseMatrix
  and Matrix, instead of repeatedly transporting semiring and ring laws by hand.
* Avoid constructing executable DenseMatrices through `ofMatrix` in hot paths;
  `ofMatrix` uses division and is primarily a conversion boundary.
* Consolidate duplicate bridge and invariance proofs when one generic theorem
  suffices, while retaining rectangular-matrix theorems that a square ring
  instance cannot express.

## Verification discipline

* Use Lean LSP diagnostics and proof goals first.
* Work on one file at a time. When changing to another file, run the appropriate
  narrow Lean check so the LSP sees the preceding file's compiled updates.
* Prefer `lake env lean <path>` for a narrow check. Use `lake build` only at a
  deliberate integration point; the active build surface excludes legacy code and
  tests for now.
