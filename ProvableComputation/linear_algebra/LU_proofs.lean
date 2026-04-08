import ProvableComputation.linear_algebra.LUFactorizationProofs

variable {R : Type} [Field R] [DecidableEq R]
variable {a b : ℕ}

/-- The `LUFactorization` output reconstructs the original matrix as `P * L * U`. -/
theorem plu_matrix_eq_matrix (M : Matrix (Fin a) (Fin b) R) :
    (LUFactorization (R := R) M).1 * (LUFactorization (R := R) M).2.1 *
      (LUFactorization (R := R) M).2.2 = M :=
  LUFactorization_reconstruct (R := R) (M := M)

/-- Square matrices satisfy the same reconstruction identity for the LU output. -/
theorem lu_matrix_eq_matrix (M : Matrix (Fin a) (Fin a) R) :
    (LUFactorization (R := R) M).1 * (LUFactorization (R := R) M).2.1 *
      (LUFactorization (R := R) M).2.2 = M :=
  plu_matrix_eq_matrix (R := R) (M := M)

/-- The permutation factor returned by `LUFactorization` is orthogonal. -/
theorem plu_permutation_orthogonal (M : Matrix (Fin a) (Fin b) R) :
    (LUFactorization (R := R) M).1.transpose * (LUFactorization (R := R) M).1 = 1 ∧
      (LUFactorization (R := R) M).1 * (LUFactorization (R := R) M).1.transpose = 1 :=
  LUFactorization_permutation_orthogonal (R := R) (M := M)

/-- The `U` factor returned by `LUFactorization` is in echelon form. -/
theorem plu_upper_isEchelon (M : Matrix (Fin a) (Fin b) R) :
    Matrix.IsEchelonForm ((LUFactorization (R := R) M).2.2) :=
  LUFactorization_upper_isEchelon (R := R) (M := M)

/-- The `L` factor returned by `LUFactorization` is unit lower triangular. -/
theorem plu_lower_isUnitLowerTriangular (M : Matrix (Fin a) (Fin b) R) :
    IsUnitLowerTriangular ((LUFactorization (R := R) M).2.1) :=
  LUFactorization_lower_isUnitLowerTriangular (R := R) (M := M)
