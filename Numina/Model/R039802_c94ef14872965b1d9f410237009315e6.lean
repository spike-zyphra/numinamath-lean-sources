import Mathlib

theorem algebra_137131 (f : ℝ → ℝ) (h₀ : MonotoneOn f (Set.Ioi 0))
    (h₁ : ∀ x y, f (x + y) = (f x * f y) / (f x + f y)) (h₂ : ∀ x, f x ≠ 0) :
    ∀ x, f x = x := by 
  have h3 := h₁ 0 0
  have h51 : f 0 ≠ 0 := h₂ 0
  have h4 : f 0 = 0 := by
    norm_num at h3 
    have h52 : f 0 + f 0 ≠ 0 := by
      have h511 : f 0 ≠ 0 := h₂ 0
      have h522 : f 0 + f 0 ≠ 0 := by
        intro h
        have : f 0 = 0 := by linarith
        contradiction
      exact h522
    field_simp [h52] at h3
    nlinarith
  contradiction