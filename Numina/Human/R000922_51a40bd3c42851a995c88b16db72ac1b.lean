import Mathlib

theorem algebra_19134 {a b c : ℝ} (h₀ : (a + 2 * b) / 2 = 7) (h₁ : (a + 2 * c) / 2 = 8) :
    (a + b + c) / 3 = 5 := by
  have : (7 : ℝ) + 8 = 7 + 8 := rfl
  nth_rw 1 [← h₀, ← h₁] at this -- Add the two equations
  ring_nf at this
  rw [this]
  norm_num