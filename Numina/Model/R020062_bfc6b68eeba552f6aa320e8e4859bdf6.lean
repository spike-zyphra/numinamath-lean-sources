import Mathlib

def f (x y : ℝ) := x * y

theorem algebra_269109 {f : ℝ → ℝ → ℝ}
    (h₀ : ∀ x, f x 0 = 1)
    (h₁ : ∀ x y z, f (f x y) z = f z (f x y) + z) :
    f 31 32 = 993 := by
  have h2 := h₁ 1 0 1
  have h3 : f 1 0 = 1 := h₀ 1
  simp [h3] at h2
  all_goals 
    linarith