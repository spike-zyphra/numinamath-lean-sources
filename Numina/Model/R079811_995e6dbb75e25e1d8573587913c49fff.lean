import Mathlib

theorem algebra_14807 {s : ℕ} (h₀ : s > 0) (h₁ : s^2 = 4 * s) : s = 4 := by
  have h5 : s > 0 := h₀
  have h6 : s * s = 4 * s := by 
    nlinarith
  have h7 : s = 4 := by
    apply (mul_right_inj' (ne_of_gt h₀)).mp
    linarith
  exact h7