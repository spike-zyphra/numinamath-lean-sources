import Mathlib

theorem algebra_17243 (t : ℝ) (h : IsLeast {t : ℝ | t > 0 ∧ -16*t^2 + 60*t = 56} t) :
    round (t * 100) / 100 = (1.75 : ℝ) := by
  have h1 : t > 0 := by
    have ht1 : t ∈ {t : ℝ | t > 0 ∧ -16*t^2 + 60*t = 56} := by 
      exact h.1 
    have ht2 : t > 0 := ht1.1 
    linarith 
  have h2 : -16*t^2 + 60*t = 56 := by 
    have ht1 : t ∈ {t : ℝ | t > 0 ∧ -16*t^2 + 60*t = 56} := by 
      exact h.1 
    have ht2 : -16*t^2 + 60*t = 56 := ht1.2 
    linarith 
  have ht1 : t ≤ 1.75 := by 
    have h3 : (1.75 : ℝ) ∈ {t : ℝ | t > 0 ∧ -16*t^2 + 60*t = 56} := by 
      constructor 
      · norm_num 
      · norm_num 
    have h4 : t ≤ (1.75 : ℝ) := by 
      apply h.2 
      exact h3 
    linarith 
  have ht2 : t ≥ 1.75 := by
    by_contra h
    push_neg at h 
    nlinarith [sq_nonneg (t - 1.75 : ℝ), sq_nonneg (t - 2 : ℝ)]
  have ht3 : t = 1.75 := by
    linarith 
  rw [ht3] 
  norm_num [round_eq]