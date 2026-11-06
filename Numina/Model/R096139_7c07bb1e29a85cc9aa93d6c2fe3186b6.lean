import Mathlib

open Real

theorem calculus_177024 {α β : ℝ} (z : ℝ) :
    deriv (fun x => exp x) z = exp z ∧ exp ((α + β) * z) = exp (α * z) * exp (β * z) := by
  constructor
  · -- Proof that deriv (fun x => exp x) z = exp z
    simp [Real.deriv_exp]
  · -- Proof that exp ((α + β) * z) = exp (α * z) * exp (β * z)
    have h1 : (α + β) * z = α * z + β * z := by ring
    rw [h1]
    rw [Real.exp_add]