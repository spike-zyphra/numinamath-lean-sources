import Mathlib

theorem algebra_216023 {f : ℝ → ℝ} (h : ∀ x, f x + (x + 0.5) * f (1 - x) = 1) :
    ∀ x, x ≠ 0.5 → f x = 1 / (0.5 - x) ∧ f 0.5 = 0.5 := by
  intro x hx
  have h1 : f 0.5 = 0.5 := by
    have eq1 := h 0.5
    norm_num at eq1 
    linarith
  have eq1 := h x
  have eq2 := h (1 - x)
  have eq3 : f x + (x + 0.5) * f (1 - x) = 1 := by 
    simpa using eq1
  have eq4 : f (1 - x) + ((1 - x) + 0.5) * f x = 1 := by 
    ring_nf at eq2 ⊢ 
    <;> simpa using eq2
  have h2 : f x = 1 / (0.5 - x) := by
    have hx1 : x - 0.5 ≠ 0 := by
      intro h'
      apply hx
      norm_num at h' ⊢
      linarith
    have eq5 : f (1 - x) = 1 - ( ( (1 - x) + 0.5 ) * f x ) := by linarith [eq4]
    rw [eq5] at eq3
    field_simp [(show (0.5 - x : ℝ) ≠ 0 by
      intro h'
      apply hx
      norm_num at h' ⊢
      linarith
    )] at *
    ring_nf at eq3 ⊢ 
    <;> nlinarith [ sq_pos_of_ne_zero (show (x - 0.5 : ℝ) ≠ 0 by
        intro h'
        apply hx 
        norm_num at h' ⊢
        linarith
    ), sq_nonneg (f x), sq_nonneg (f (1 - x) ) ]
  constructor
  · exact h2 
  · exact h1