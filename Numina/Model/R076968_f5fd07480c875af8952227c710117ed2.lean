import Mathlib

theorem algebra_13238 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y) (h2 : f 2 = 3) :
    f 6 = 27 := by
  have h4 : f 4 = 9 := by
    have h4_eq : f 4 = f 2 * f 2 := by
      specialize h 2 2
      norm_num at h ⊢
      exact h
    rw [h2] at h4_eq
    norm_num at h4_eq ⊢
    exact h4_eq
  have h6_eq : f 6 = f 2 * f 4 := by
    specialize h 2 4
    norm_num at h ⊢
    exact h
  rw [h2, h4] at h6_eq
  norm_num at h6_eq ⊢
  exact h6_eq