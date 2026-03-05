import ProvableComputation.linear_algebra.Determinant
import ProvableComputation.linear_algebra.LUFactorization

#eval swapRow sampleMatrix 1 2
#eval factor sampleMatrix 1 2
#eval replace sampleMatrix 1 2 3
#eval replace sampleMatrix 1 1 3
#eval factor sampleMatrix 1 4
#eval checkPivot sampleMatrix 0 0
#eval (eliminateCol sampleMatrix 0 0 List.nil true).1
#eval (reducedRowEchelonForm sampleMatrix).1

#time #eval toString (gaussDet matrix2)
#time #eval toString (matrix2.det)

#time #eval LUFactorization sampleMatrix
#time #eval (LUFactorization sampleMatrix).1 * (LUFactorization sampleMatrix).2.1 *
  (LUFactorization sampleMatrix).2.2

#time #eval LUFactorization sampleMatrix2
#time #eval (LUFactorization sampleMatrix2).1 * (LUFactorization sampleMatrix2).2.1 *
  (LUFactorization sampleMatrix2).2.2

#time #eval LUFactorization sampleMatrix4

#time #eval LUFactorization sampleMatrix3
#time #eval (LUFactorization sampleMatrix3).1 * (LUFactorization sampleMatrix3).2.1 *
  (LUFactorization sampleMatrix3).2.2
