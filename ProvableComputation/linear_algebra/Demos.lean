import ProvableComputation.linear_algebra.Determinant
import ProvableComputation.linear_algebra.LUFactorization

def luCounterexample : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 0, 0],
    ![2, 1, 0],
    ![3, 5, 1]]

def luNonsquare : Matrix (Fin 3) (Fin 4) Rat :=
  ![![1, 0, 0, 7],
    ![2, 1, 0, 8],
    ![3, 5, 1, 9]]

private def reconstructLU {R : Type} [Field R] [DecidableEq R] {a b : Nat}
    (M : Matrix (Fin a) (Fin b) R) : Matrix (Fin a) (Fin b) R :=
  let lu := LUFactorization M
  lu.1 * lu.2.1 * lu.2.2

#eval swapRow sampleMatrix 1 2
#eval factor sampleMatrix 1 2
#eval replace sampleMatrix 1 2 3
#eval replace sampleMatrix 1 1 3
#eval factor sampleMatrix 1 4
#eval checkPivot sampleMatrix 0 0
#eval (eliminateCol sampleMatrix 0 0 List.nil true).1
#eval (rowEchelonForm sampleMatrix).1
#eval (reducedRowEchelonForm sampleMatrix).1
#eval (rowEchelonForm sampleMatrix4).1

-- Determinant runtime tests

-- 3x3 matrices
#time #eval LUDet sampleMatrix
#time #eval (gaussDet sampleMatrix)
#time #eval (sampleMatrix.det)
#time #eval LUDet sampleMatrix2
#time #eval (gaussDet sampleMatrix2)
#time #eval (sampleMatrix2.det)

-- 4x4 matrix
#time #eval LUDet sampleMatrix4
#time #eval (gaussDet sampleMatrix4)
#time #eval (sampleMatrix4.det)

-- 5x5 matrix
#time #eval LUDet matrix2
#time #eval (gaussDet matrix2)
#time #eval (matrix2.det)

-- 10x10 matrices
-- Stack overflow, original determinant computation can't handle 10x10 matrices
#time #eval LUDet sampleMatrix3
#time #eval (gaussDet sampleMatrix3)
--#time #eval (sampleMatrix3.det)
#time #eval LUDet matrix3
#time #eval (gaussDet matrix3)
--#time #eval (matrix3.det)

#time #eval LUFactorization sampleMatrix
#time #eval (LUFactorization sampleMatrix).1 * (LUFactorization sampleMatrix).2.1 *
  (LUFactorization sampleMatrix).2.2

#time #eval LUFactorization sampleMatrix2
#time #eval (LUFactorization sampleMatrix2).1 * (LUFactorization sampleMatrix2).2.1 *
  (LUFactorization sampleMatrix2).2.2

#time #eval LUFactorization sampleMatrix4
#time #eval (LUFactorization sampleMatrix4).1 * (LUFactorization sampleMatrix4).2.1 *
  (LUFactorization sampleMatrix4).2.2

#time #eval LUFactorization sampleMatrix3
#time #eval (LUFactorization sampleMatrix3).1 * (LUFactorization sampleMatrix3).2.1 *
  (LUFactorization sampleMatrix3).2.2

#eval LUFactorization luCounterexample
#eval reconstructLU luCounterexample
#eval decide (reconstructLU luCounterexample = luCounterexample)

#eval LUFactorization luNonsquare
#eval reconstructLU luNonsquare
#eval decide (reconstructLU luNonsquare = luNonsquare)
