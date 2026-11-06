import Mathlib

theorem algebra_18548 (f : ℝ → ℝ → ℝ) (hf : f = fun x y => y^2 - x + 5 * y - 25) :
    ∀ x y, f x y = 0 ↔ (x = y^2 + 5 * y - 25) := by 
  intro x y
  constructor
  · -- Assume h0 : f x y = 0, we need to prove x = y^2 + 5 * y - 25
    intro h0
    rw [hf] at h0
    simp at h0 
    linarith
  · -- Assume h_eq : x = y^2 + 5 * y - 25, we need to prove f x y = 0
    intro h_eq
    rw [hf]
    simp [h_eq]
    <;> linarith