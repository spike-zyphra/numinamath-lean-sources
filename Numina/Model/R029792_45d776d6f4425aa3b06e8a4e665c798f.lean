import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10669 {x y : ℝ} (hy : y ∈ Icc 0 (π/2)) (h1 : x + sin y = 2008)
    (h2 : x + 2008 * cos y = 2007) : x + y = 2007 + π/2 := by 
  rcases hy with ⟨hy1, hy2⟩
  have eq1 : sin y - 2008 * cos y = 1 := by
    nlinarith [h1, h2]
  have h3 : sin y ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : cos y ≥ 0 := by 
    apply cos_nonneg_of_neg_pi_div_two_le_of_le
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h5 : sin y ≤ 1 := by 
    linarith [sin_le_one y]
  have h6 : cos y = 0 := by
    nlinarith [eq1, h4, h5, Real.sin_sq_add_cos_sq y]
  have h7 : sin y = 1 := by 
    have h8 : sin y ^ 2 + cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    rw [h6] at h8
    have h9 : sin y ^ 2 = 1 := by 
      nlinarith 
    have h10 : sin y = 1 := by 
      nlinarith [h3]
    exact h10 
  have hx : x = 2007 := by 
    linarith [h1, h7]
  have hy3 : y = π / 2 := by 
    by_cases h : y < π / 2 
    · -- Assume y < π/2, then cos y > 0, contradiction 
      have hcos : cos y > 0 := by 
        apply cos_pos_of_mem_Ioo 
        constructor
        · -- Show that -π/2 < y 
          nlinarith [Real.pi_pos, show y ≥ 0 by linarith]
        · -- Show that y < π/2 
          linarith [Real.pi_pos]
      linarith [h6, hcos] 
    · -- y ≥ π/2 
      have hy4 : y ≥ π / 2 := by linarith 
      have hy5 : y ≤ π / 2 := by linarith [Real.pi_pos] 
      have hy6 : y = π / 2 := by linarith 
      exact hy6 
  rw [hx, hy3]
  all_goals linarith [Real.pi_pos]