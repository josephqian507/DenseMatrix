import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Determinant
import Init.Data.Random

import ProvableComputation.linear_algebra.Determinant

-- A simple way to generate a "random" matrix using a pseudo-random seed
def randomMatrix (n : Nat) (seed : Nat) : Matrix (Fin n) (Fin n) Rat :=
  Matrix.of fun i j =>
    let gen := mkStdGen (seed + i.val * n + j.val)
    let (numNat, gen) := randNat gen 0 100
    let (isNeg, gen) := randNat gen 0 1
    let num : Int := if isNeg == 0 then (numNat : Int) else -(numNat : Int)
    let (denom, _) := randNat gen 1 100
    mkRat num denom

def benchmark (n : Nat) (samples : Nat) : IO Unit := do
  let mut totalRatio : Float := 0
  let mut validSamples : Nat := 0

  for i in [0:samples] do
    let mat := randomMatrix n (i * 12345)

    -- Measure gaussDet
    let startLUDet ← IO.monoNanosNow
    let _ := LUDet mat
    let endLUDet ← IO.monoNanosNow
    let timeLUDet := (endLUDet - startLUDet).toFloat
    IO.println s!"LU time: {timeLUDet}"

    -- Measure Matrix.det
    let startLeibnizDet ← IO.monoNanosNow
    let _ := mat.det
    let endLeibnizDet ← IO.monoNanosNow
    let timeLeibnizDet := (endLeibnizDet - startLeibnizDet).toFloat
    IO.println s!"det time: {timeLeibnizDet}"

    if timeLUDet > 0 then
      totalRatio := totalRatio + (timeLeibnizDet / timeLUDet)
      validSamples := validSamples + 1

  if validSamples > 0 then
    let avg := totalRatio / validSamples.toFloat
    IO.println s!"Average Ratio (Matrix.det / LUDet) for {n}x{n}: {avg}"
  else
    IO.println "Samples ran too quickly to measure in ms."

-- Run with a small n (like 6 or 7) to avoid the n! explosion
#time #eval benchmark 10 10
