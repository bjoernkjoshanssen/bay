import Mathlib.Topology.Clopen
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.NormNum.Prime
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.PosDef

/- We verify the numerical computation on page 10 of
[Interpolating between the Jaccard distance and
an analogue of the normalized information
distance]. We also show that it is false if we take division to be over ℕ.

-/

example : (21:ℚ)^3 / (101^3 + 21^3) > 2^3 * (10^3 + 11^3)/(101^3 + 102^3 + 10^3 + 11^3) := by
  ring_nf
  linarith

example : 21^3 / (101^3 + 21^3) ≤ 2^3 * (10^3 + 11^3)/(101^3 + 102^3 + 10^3 + 11^3) := by
  ring_nf
  linarith
