import Mathlib

theorem algebra_11645 (f : ℝ → ℝ) (h₀ : ∀ x y, 0 < x → 0 < y → x * f y - y * f x = f (x / y)) :
    f 100 = 0 := by
  have h1 : f 1 = 0 := by
    specialize h₀ 1 1 (by norm_num) (by norm_num)
    norm_num at h₀
    linarith
  have h2 : ∀ x, 0 < x → f x = 0 := by
    intro x hx
    specialize h₀ x 1 hx (by norm_num)
    rw [h1] at h₀
    norm_num at h₀
    linarith
  specialize h2 100 (by norm_num)
  exact h2