/-
Copyright (c) 2026 Provable Computation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Provable Computation contributors
-/

-- Public library surface: the root module re-exports the executable algorithms,
-- their correctness layers, and the dense backend used by the Matrix wrappers.
import ProvableComputation.certifiable_euclidean_alg
import ProvableComputation.LinearAlgebra.DenseMatrix.Defs
import ProvableComputation.LinearAlgebra.DenseMatrix.Elementary
import ProvableComputation.LinearAlgebra.Determinant.Basic
import ProvableComputation.LinearAlgebra.Determinant.Correctness
import ProvableComputation.LinearAlgebra.Echelon
import ProvableComputation.LinearAlgebra.GaussianElimination.Elementary
import ProvableComputation.LinearAlgebra.GaussianElimination.Rref
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefCorrectness
import ProvableComputation.LinearAlgebra.GaussianElimination.RrefUniqueness
import ProvableComputation.LinearAlgebra.LU.Basic
import ProvableComputation.LinearAlgebra.LU.Correctness

/-!
# Provable Computation

Root module exporting the library surface.
-/
