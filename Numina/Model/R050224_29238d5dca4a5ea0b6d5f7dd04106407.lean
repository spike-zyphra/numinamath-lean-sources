import Mathlib

theorem algebra_167901 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y + 80 * x * y) (h' : f 0.25 = 2) :
    f 1 = 38 := by
  have f05 : f 0.5 = 9 := by
    specialize h 0.25 0.25
    rw [show (0.25 + 0.25 : ℝ) = (0.5 : ℝ) by norm_num, h'] at h
    norm_num at h ⊢
    linarith
  have f075 : f 0.75 = 21 := by
    specialize h 0.5 0.25
    rw [show (0.5 + 0.25 : ℝ) = (0.75 : ℝ) by norm_num, f05, h'] at h
    norm_num at h ⊢
    linarith
  have h1 : f 1 = 38 := by
    specialize h 0.75 0.25
    rw [show (0.75 + 0.25 : ℝ) = (1 : ℝ) by norm_num, f075, h'] at h
    norm_num at h ⊢
    linarith
  exact h1