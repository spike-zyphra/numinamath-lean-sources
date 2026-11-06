import Mathlib

open Real Set
open scoped Real

theorem inequalities_312542 (k : ℝ) :
  (∃ x, (1 + sin x) / (2 + cos x) ≥ k) ↔ k ≤ 4 / 3 := by
  constructor
  · -- Forward direction: prove that if there exists such an x, then k ≤ 4/3.
    intro h
    rcases h with ⟨x, hx⟩
    by_contra h1
    push_neg at h1
    have h2 : (2 + cos x) > 0 := by
      have h3 : cos x ≥ -1 := by linarith [neg_one_le_cos x, cos_le_one x]
      nlinarith
    have h3 : (1 + sin x) ≥ k * (2 + cos x) := by
      have h4 : (2 + cos x) > 0 := h2
      apply (le_div_iff₀ h4).mp at hx
      linarith
    have h4 : (k) > 4 / 3 := by linarith
    have h5 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x - 3 / 5), sq_nonneg (cos x + 4 / 5), sq_nonneg (k - 4 / 3), sq_nonneg (sin x * 5 - 3), sq_nonneg (cos x * 5 + 4), Real.sin_sq_add_cos_sq x, Real.sin_le_one x, Real.neg_one_le_sin x, Real.cos_le_one x, Real.neg_one_le_cos x, mul_self_nonneg (sin x - 3 / 5), mul_self_nonneg (cos x + 4 / 5)]
  · -- Backward direction: prove that if k ≤ 4/3, then there exists such an x.
    intro h
    use Real.pi / 2 + Real.arcsin (4 / 5)
    have h1 : sin (Real.pi / 2 + Real.arcsin (4 / 5)) = 3 / 5 := by
      have hsin : sin (Real.pi / 2 + Real.arcsin (4 / 5)) = cos (Real.arcsin (4 / 5)) := by 
        rw [sin_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals linarith
      have hcos1 : cos (Real.arcsin (4 / 5)) = Real.sqrt (1 - (4/5)^2) := by
        rw [cos_arcsin]
      have hcos2 : Real.sqrt (1 - (4/5)^2) = 3/5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [hsin, hcos1, hcos2]
    have h2 : cos (Real.pi / 2 + Real.arcsin (4 / 5)) = -4 / 5 := by
      have hcos : cos (Real.pi / 2 + Real.arcsin (4 / 5)) = - sin (Real.arcsin (4 / 5)) := by 
        rw [cos_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals linarith
      have hsin1 : sin (Real.arcsin (4 / 5)) = (4/5 : ℝ) := by 
        apply sin_arcsin
        all_goals norm_num
      rw [hcos, hsin1]
      all_goals norm_num
    rw [h1, h2]
    have h3 : (k : ℝ) ≤ 4 / 3 := by linarith 
    norm_num at *
    all_goals nlinarith