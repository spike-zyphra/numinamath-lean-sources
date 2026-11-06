import Mathlib

theorem algebra_222303 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 1 → x + f x + 2 * f ((x + 2009) / (x - 1)) = 2010) :
    ∀ x, x ≠ 1 → f x = (x ^ 2 + 2007 * x - 6028) / (3 * (x - 1)) := by
  intro x hx
  have eq1 := hf x hx
  have eq2 : x - 1 ≠ 0 := by 
    intro h
    apply hx
    linarith
  have y_neq_1 : (x + 2009) / (x - 1) ≠ 1 := by
    by_contra h_eq1
    have h_eq2 : x + 2009 = x - 1 := by
      field_simp [(show x - 1 ≠ 0 by assumption)] at h_eq1 ⊢
      linarith
    linarith
  have eq3 := hf ((x + 2009) / (x - 1)) y_neq_1
  have eq4 : ((x + 2009) / (x - 1) + 2009) / ((x + 2009) / (x - 1) - 1) = x := by
    field_simp [(show x - 1 ≠ 0 by assumption), (show (x + 2009) / (x - 1) - 1 ≠ 0 by 
      by_contra h_eq1
      have h_eq2 : (x + 2009) / (x - 1) = 1 := by 
        field_simp [(show x - 1 ≠ 0 by assumption)] at h_eq1 ⊢
        linarith
      have h_eq3 : (x + 2009) / (x - 1) ≠ 1 := y_neq_1 
      contradiction
    )]
    ring
  simp [eq4] at eq3
  field_simp [(show x - 1 ≠ 0 by assumption)] at eq1 eq3 ⊢
  ring_nf at eq1 eq3 ⊢
  nlinarith [ sq_pos_of_ne_zero (show x - 1 ≠ 0 by assumption) ]