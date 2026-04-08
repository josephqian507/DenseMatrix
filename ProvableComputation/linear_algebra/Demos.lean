import Mathlib.Algebra.Field.Rat

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

def sampleMatrix2 : Matrix (Fin 3) (Fin 3) Rat :=
  ![![1, 2, 3],
    ![4, 8, 12],
    ![2, 5, 6]]

def sampleMatrix3 : Matrix (Fin 10) (Fin 10) Rat :=
  ![![9, 8, 6, 9, 7, 4, 6, 8, 4, 7],
    ![27, 30, 22, 34, 29, 17, 23, 31, 20, 24],
    ![36, 86, 61, 106, 134, 66, 77, 100, 97, 64],
    ![9, 212, 153, 327, 658, 236, 272, 307, 384, 215],
    ![27, 24, 22, 61, 168, 52, 74, 65, 71, 79],
    ![0, 180, 124, 244, 387, 198, 214, 258, 304, 150],
    ![9, 26, 20, 71, 152, 148, 193, 181, 247, 169],
    ![27, 78, 58, 133, 262, 184, 307, 296, 753, 237],
    ![27, 30, 54, 267, 1141, 316, 511, 427, 943, 514],
    ![18, 16, 16, 52, 169, 96, 216, 207, 680, 240]]

def sampleMatrix4 : Matrix (Fin 4) (Fin 4) Rat :=
  ![![3, 5, 1, 9],
    ![94, 2, 8, 0],
    ![9, 3, 2, 9],
    ![45, 3, 9, 8]]

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
#time #eval reconstructLU sampleMatrix
#eval decide (reconstructLU sampleMatrix = sampleMatrix)

#time #eval LUFactorization sampleMatrix2
#time #eval reconstructLU sampleMatrix2
#eval decide (reconstructLU sampleMatrix2 = sampleMatrix2)

#time #eval LUFactorization sampleMatrix4
#time #eval reconstructLU sampleMatrix4
#eval decide (reconstructLU sampleMatrix4 = sampleMatrix4)

#time #eval LUFactorization sampleMatrix3
#time #eval reconstructLU sampleMatrix3
#eval decide (reconstructLU sampleMatrix3 = sampleMatrix3)

#eval LUFactorization luCounterexample
#eval reconstructLU luCounterexample
#eval decide (reconstructLU luCounterexample = luCounterexample)

#eval LUFactorization luNonsquare
#eval reconstructLU luNonsquare
#eval decide (reconstructLU luNonsquare = luNonsquare)
