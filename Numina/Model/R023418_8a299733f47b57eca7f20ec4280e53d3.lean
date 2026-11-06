import Mathlib

open Real Set
open scoped Real

theorem algebra_314864 (x : ℝ) (hx : x ∈ Icc 0 Real.pi) (h : 3 * sin (x / 2) = sqrt (1 + sin x) - sqrt (1 - sin x)) :
    tan x = 0 := by
  rcases hx with ⟨hx0, hxpi⟩
  have h1 : 0 ≤ x := by linarith
  have h2 : x ≤ Real.pi := by linarith
  have h3 : (3 * sin (x / 2)) ^ 2 = (sqrt (1 + sin x) - sqrt (1 - sin x)) ^ 2 := by 
    rw [h]
  have h5 : (sqrt (1 + sin x)) ^ 2 = 1 + sin x := by 
    apply Real.sq_sqrt 
    have h6 : -1 ≤ sin x := by 
      linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    have h7 : 1 + sin x ≥ 0 := by linarith 
    linarith
  have h8 : (sqrt (1 - sin x)) ^ 2 = 1 - sin x := by 
    apply Real.sq_sqrt 
    have h9 : sin x ≤ 1 := by 
      linarith [Real.sin_le_one x]
    have h10 : 1 - sin x ≥ 0 := by linarith 
    linarith 
  have h10 : (sqrt (1 + sin x) - sqrt (1 - sin x)) ^ 2 = (1 + sin x) + (1 - sin x) - 2 * (sqrt (1 + sin x) * sqrt (1 - sin x)) := by 
    calc 
      (sqrt (1 + sin x) - sqrt (1 - sin x)) ^ 2 
          = (sqrt (1 + sin x)) ^ 2 + (sqrt (1 - sin x)) ^ 2 - 2 * (sqrt (1 + sin x) * sqrt (1 - sin x)) := by ring 
      _ = (1 + sin x) + (1 - sin x) - 2 * (sqrt (1 + sin x) * sqrt (1 - sin x)) := by 
        rw [h5, h8]
  rw [h10] at h3 
  have h12 : sqrt (1 + sin x) * sqrt (1 - sin x) = abs (cos x) := by
    have h11 : sqrt (1 + sin x) * sqrt (1 - sin x) = Real.sqrt (1 - sin x ^ 2) := by 
      have h12 : 1 - sin x ^ 2 = (1 + sin x) * (1 - sin x) := by 
        nlinarith 
      rw [h12] 
      all_goals 
        rw [← Real.sqrt_mul (by 
          have h4 : 1 + sin x ≥ 0 := by 
            nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
          linarith 
        )]
    have h14 : Real.sqrt (1 - sin x ^ 2) = Real.sqrt (cos x ^ 2) := by 
      have h20 : cos x ^ 2 = 1 - sin x ^ 2 := by 
        have : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
        linarith 
      rw [h20] 
    rw [h11, h14] 
    rw [Real.sqrt_sq_eq_abs]
  rw [h12] at h3 
  by_cases h13 : cos x ≥ 0 
  · -- cos x ≥ 0, so |cos x| = cos x 
    rw [abs_of_nonneg h13] at h3 
    have h13a : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by 
      have h13b : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by 
        have h16b : sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by 
          rw [Real.sin_sq_eq_half_sub]
          ring_nf 
        linarith 
      linarith 
    have h14 : cos x = 1 := by 
      nlinarith [h13a] 
    have h15 : sin x = 0 := by 
      have h14a : cos x = 1 := h14 
      have : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
      rw [h14a] at this 
      have h16a : sin x = 0 := by 
        nlinarith [h14a, sq_nonneg (sin x)] 
      linarith 
    have h16 : tan x = 0 := by 
      rw [tan_eq_sin_div_cos] 
      rw [h15, h14] 
      norm_num 
    linarith 
  · -- cos x < 0, so |cos x| = -cos x 
    have h14 : cos x < 0 := by 
      by_contra h 
      push_neg at h 
      have : cos x ≥ 0 := by 
        nlinarith 
      linarith 
    rw [abs_of_neg h14] at h3 
    have h13a : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by 
      have h13b : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by 
        have h16b : sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by 
          rw [Real.sin_sq_eq_half_sub]
          ring_nf 
        linarith 
      linarith 
    -- derive inconsistency 
    nlinarith [sq_nonneg (cos x - 1), sq_nonneg (sin (x / 2) - 0), Real.sin_le_one (x / 2), Real.sin_sq_add_cos_sq (x / 2), Real.sin_sq_add_cos_sq x]