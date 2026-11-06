import Mathlib

open Finset BigOperators

/- Generalize the problem of finding a formula for the dot product of two vectors, \((a_{1}, a_{2}, \ldots, a_{n})\) and \([a_{1}, a_{2}, \ldots, a_{n}]\), where \(a_{1}, a_{2}, \ldots, a_{n}\) are positive integers.-/
theorem number_theory_4588 {n : ℕ} (A : Fin n → ℝ ) :
    dotProduct A A = ∑ i : Fin n, (A i)^2 := by
  -- exact `Matrix.dotProduct` in Mathlib
  unfold dotProduct
  ring_nf
