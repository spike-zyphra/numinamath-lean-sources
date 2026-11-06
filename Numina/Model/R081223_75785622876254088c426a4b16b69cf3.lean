import Mathlib

theorem algebra_15744 {f : ℝ → ℝ} (h : ∀ x, f (x + f x) = 4 * f x) (h' : f 1 = 4) :
    f 21 = 64 := by
  have h1 : f 5 = 16 := by
    specialize h 1
    rw [h'] at h
    norm_num at h
    linarith
  have h2 : f 21 = 64 := by
    specialize h 5
    rw [h1] at h
    norm_num at h
    linarith
  exact h2