import Mathlib

theorem algebra_317965 (α : ℝ) (h : Real.sin α + Real.cos α = 7 / 5) (h' : Real.tan α > 1) :
    Real.cos α = 3 / 5 := by
  have h1 : Real.cos α ≠ 0 := by
    by_contra h2
    have htan : Real.tan α = 0 := by 
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    linarith 
  have htan : Real.tan α = Real.sin α / Real.cos α := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at h'
  by_cases hcos : Real.cos α > 0
  · -- Case where cos α > 0
    have h2 : Real.sin α > Real.cos α := by 
      apply (lt_div_iff₀ hcos).mp at h'
      all_goals nlinarith
    have eq1 : Real.sin α + Real.cos α = 7 / 5 := h
    have eq2 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have hcos2 : Real.cos α = 3 / 5 := by
      nlinarith [sq_nonneg (Real.sin α - Real.cos α), sq_pos_of_pos hcos, Real.sin_sq_add_cos_sq α]
    exact hcos2
  · -- Case where cos α ≤ 0
    have hcos2 : Real.cos α ≤ 0 := by
      by_cases hcos' : Real.cos α < 0 
      · linarith
      · -- Real.cos α = 0
        have : Real.cos α = 0 := by linarith
        contradiction
    have hcos_neg : Real.cos α < 0 := by
      by_contra hcos'
      push_neg at hcos'
      have : Real.cos α = 0 := by linarith [hcos2, hcos']
      contradiction
    -- From h': sin α / cos α > 1 and cos α < 0 implies sin α < cos α
    have h3 : Real.sin α < Real.cos α := by 
      apply (lt_div_iff_of_neg' hcos_neg).mp at h'
      all_goals nlinarith
    -- But we have h : Real.sin α + Real.cos α = 7 / 5 > 0 
    -- and h3 : Real.sin α < Real.cos α with Real.cos α < 0
    -- This leads to a contradiction since Real.sin α < Real.cos α < 0
    -- implies Real.sin α + Real.cos α < 0, contradicting h
    nlinarith [Real.sin_sq_add_cos_sq α, h3, hcos2]