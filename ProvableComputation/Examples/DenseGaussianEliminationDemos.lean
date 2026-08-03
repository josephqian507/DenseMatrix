import Mathlib.Algebra.Field.Rat

import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.GaussianElimination.Rref

/-!
# Gaussian Elimination Demos

This module contains executable examples and timing checks for the Gaussian elimination,
LU factorization, and determinant code. It is intentionally kept out of the core library
import surface.
-/

open DenseMatrix

/-- A small `3 × 3` matrix used in Gaussian elimination examples. -/
def sampleMatrix : DenseMatrix 3 3 Rat :=
  ofMatrix (![![1, 2, 3],
            ![2, 5, 6],
            ![4, 8, 12]])

/-- A `3 × 3` matrix with dependent rows used in determinant timings. -/
def sampleMatrix2 : DenseMatrix 3 3 Rat :=
  ofMatrix (![![1, 2, 3],
            ![4, 8, 12],
            ![2, 5, 6]])

/-- A larger `10 × 10` matrix used for runtime comparisons. -/
def sampleMatrix3 : DenseMatrix 10 10 Rat :=
  ofMatrix (![![9, 8, 6, 9, 7, 4, 6, 8, 4, 7],
            ![27, 30, 22, 34, 29, 17, 23, 31, 20, 24],
            ![36, 86, 61, 106, 134, 66, 77, 100, 97, 64],
            ![9, 212, 153, 327, 658, 236, 272, 307, 384, 215],
            ![27, 24, 22, 61, 168, 52, 74, 65, 71, 79],
            ![0, 180, 124, 244, 387, 198, 214, 258, 304, 150],
            ![9, 26, 20, 71, 152, 148, 193, 181, 247, 169],
            ![27, 78, 58, 133, 262, 184, 307, 296, 753, 237],
            ![27, 30, 54, 267, 1141, 316, 511, 427, 943, 514],
            ![18, 16, 16, 52, 169, 96, 216, 207, 680, 240]])

/-- A `4 × 4` matrix used in example row-reduction and determinant runs. -/
def sampleMatrix4 : DenseMatrix 4 4 Rat :=
  ofMatrix (![![3, 5, 1, 9],
            ![94, 2, 8, 0],
            ![9, 3, 2, 9],
            ![45, 3, 9, 8]])

/-- A `5 × 5` matrix used in determinant runtime checks. -/
def sampleMatrix5 : DenseMatrix 5 5 Rat :=
  ofMatrix (![![3, -2, 5, 1, 4],
            ![1, 6, -3, 2, 0],
            ![4, 0, 2, -1, 5],
            ![-2, 3, 1, 4, -3],
            ![5, 1, -4, 0, 2]])

/-- A dense `10 × 10` matrix used in determinant runtime checks. -/
def sampleMatrix6 : DenseMatrix 10 10 Rat :=
  ofMatrix (![![1, 2, -1, 0, 3, 4, -2, 1, 5, 0],
            ![0, -3, 4, 1, 2, -1, 0, 6, -2, 3],
            ![5, 1, 0, -2, 4, 3, 1, -1, 0, 2],
            ![-2, 0, 3, 5, -1, 2, 4, 0, 1, -3],
            ![4, -1, 2, 0, 6, 1, -3, 5, 0, 2],
            ![1, 3, 0, -1, 2, 5, 4, -2, 6, 0],
            ![0, 2, -4, 3, 1, 0, 5, 2, -1, 4],
            ![3, 0, 1, 4, -2, 6, 0, 1, 2, -1],
            ![-1, 4, 2, 0, 5, -3, 1, 0, 3, 6],
            ![2, -2, 5, 1, 0, 4, -1, 3, 0, 1]])

#time #eval toString (rowEchelonForm sampleMatrix).matrix
#time #eval toString (reducedRowEchelonForm sampleMatrix).matrix
#time #eval toString (rowEchelonForm sampleMatrix2).matrix
#time #eval toString (reducedRowEchelonForm sampleMatrix2).matrix
#time #eval toString (rowEchelonForm sampleMatrix3).matrix
#time #eval toString (reducedRowEchelonForm sampleMatrix3).matrix
#time #eval toString (rowEchelonForm sampleMatrix4).matrix
#time #eval toString (reducedRowEchelonForm sampleMatrix4).matrix
#time #eval toString (rowEchelonForm sampleMatrix5).matrix
#time #eval toString (reducedRowEchelonForm sampleMatrix5).matrix
#time #eval toString (rowEchelonForm sampleMatrix6).matrix
#time #eval toString (reducedRowEchelonForm sampleMatrix6).matrix
