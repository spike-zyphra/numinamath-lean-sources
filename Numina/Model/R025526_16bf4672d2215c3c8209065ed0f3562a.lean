import Mathlib

open Real Set
open scoped Real

theorem algebra_326023 : cos ((arccos 0.25 - arccos 0.875)/2) = 3 * sqrt 6 / 8 := by
  have h1 : cos (arccos 0.25) = 0.25 := by
    apply cos_arccos
    all_goals norm_num
  -- $\cos(\arccos 0.25) = 0.25$.
  have h2 : cos (arccos 0.875) = 0.875 := by
    apply cos_arccos
    all_goals norm_num
  -- $\cos(\arccos 0.875) = 0.875$.
  have h3 : sin (arccos 0.25) = Real.sqrt 15 / 4 := by
    have h4 : sin (arccos 0.25) = Real.sqrt (1 - (0.25: ℝ) ^ 2) := by
      rw [sin_arccos]
    rw [h4]
    have h5 : (1 - (0.25 : ℝ) ^ 2) = (15 / 16 : ℝ) := by
      norm_num
    rw [h5]
    have h6 : Real.sqrt (15 / 16 : ℝ) = Real.sqrt 15 / 4 := by
      rw [show (15 / 16 : ℝ) = (15 : ℝ) / (4 ^ 2) by ring]
      field_simp [Real.sqrt_div, Real.sqrt_sq]
    rw [h6]
    <;> norm_num
    all_goals norm_num [Real.sqrt_pos]
  -- $\sin(\arccos 0.25) = \sqrt{15}/4$.
  have h7 : sin (arccos 0.875) = Real.sqrt 15 / 8 := by
    have h8 : sin (arccos 0.875) = Real.sqrt (1 - (0.875: ℝ) ^ 2) := by
      rw [sin_arccos]
    rw [h8]
    have h9 : (1 - (0.875 : ℝ) ^ 2) = (15 / 64 : ℝ) := by
      norm_num
    rw [h9]
    have h10 : Real.sqrt (15 / 64 : ℝ) = Real.sqrt 15 / 8 := by
      rw [show (15 / 64 : ℝ) = (15 : ℝ) / (8 ^ 2) by ring]
      field_simp [Real.sqrt_div, Real.sqrt_sq]
    rw [h10]
    <;> norm_num
    all_goals norm_num [Real.sqrt_pos]
  -- $\sin(\arccos 0.875) = \sqrt{15}/8$.
  have h11 : cos (arccos 0.25 - arccos 0.875) = 0.25 * 0.875 + (Real.sqrt 15 / 4) * (Real.sqrt 15 / 8) := by
    rw [cos_sub]
    rw [h1, h2]
    rw [h3, h7]
    all_goals norm_num
    all_goals norm_num [Real.sqrt_pos]
  -- $\cos(\arccos 0.25 - \arccos 0.875) = 0.25 * 0.875 + (\sqrt{15}/4) * (\sqrt{15}/8)$.
  have h12 : cos (arccos 0.25 - arccos 0.875) = 11 / 16 := by
    rw [h11]
    have h13 : (0.25 : ℝ) * (0.875 : ℝ) = (7 / 32 : ℝ) := by norm_num
    have h14 : (Real.sqrt 15 / 4 : ℝ) * (Real.sqrt 15 / 8 : ℝ) = (15 / 32 : ℝ) := by
      calc
        (Real.sqrt 15 / 4 : ℝ) * (Real.sqrt 15 / 8 : ℝ) = (Real.sqrt 15 * Real.sqrt 15) / 32 := by ring_nf
        _ = (Real.sqrt 15 ^ 2) / 32 := by ring_nf
        _ = (15 : ℝ) / 32 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
    rw [h13, h14]
    norm_num
  -- $\cos(\arccos 0.25 - \arccos 0.875) = 11/16$.
  have h15 : cos ((arccos 0.25 - arccos 0.875)/2) = Real.sqrt ((1 + cos (arccos 0.25 - arccos 0.875)) / 2) := by
    have h16 : cos ((arccos 0.25 - arccos 0.875)/2) = Real.sqrt ((1 + cos (arccos 0.25 - arccos 0.875)) / 2) := by
      have h17 : cos ((arccos 0.25 - arccos 0.875)/2) ≥ 0 := by
        apply cos_nonneg_of_neg_pi_div_two_le_of_le
        all_goals
          have h18 : arccos 0.25 ≥ 0 := by apply arccos_nonneg
          have h19 : arccos 0.875 ≥ 0 := by apply arccos_nonneg
          have h20 : arccos 0.25 ≤ Real.pi := by apply arccos_le_pi
          have h21 : arccos 0.875 ≤ Real.pi := by apply arccos_le_pi
          nlinarith [Real.pi_pos]
      have h18 : cos ((arccos 0.25 - arccos 0.875)/2) ^ 2 = (1 + cos (arccos 0.25 - arccos 0.875)) / 2 := by
        have h19 : cos ((arccos 0.25 - arccos 0.875)/2) ^ 2 = (1 + cos (arccos 0.25 - arccos 0.875)) / 2 := by
          have h20 : sin ((arccos 0.25 - arccos 0.875)/2) ^ 2 + cos ((arccos 0.25 - arccos 0.875)/2) ^ 2 = 1 := by
            exact Real.sin_sq_add_cos_sq ((arccos 0.25 - arccos 0.875)/2)
          have h21 : cos (arccos 0.25 - arccos 0.875) = 2 * cos ((arccos 0.25 - arccos 0.875)/2)^2 - 1 := by
            rw [←Real.cos_two_mul ((arccos 0.25 - arccos 0.875)/2)]
            ring_nf
          linarith
        linarith
      have h19 : cos ((arccos 0.25 - arccos 0.875)/2) = Real.sqrt ((1 + cos (arccos 0.25 - arccos 0.875)) / 2) := by
        rw [←h18]
        field_simp [h17]
      exact h19
    exact h16
  -- $\cos(\theta/2) = \sqrt{\frac{1 + \cos(\theta)}{2}}$
  rw [h15]
  rw [show cos (arccos 0.25 - arccos 0.875) = (11 / 16 : ℝ) by linarith [h12]]
  -- Compute $\sqrt{\frac{1 + \frac{11}{16}}{2}} = \sqrt{\frac{27}{32}}$
  have h18 : Real.sqrt ((1 + (11 / 16 : ℝ)) / 2) = (3 * Real.sqrt 6 / 8 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num [Real.sqrt_pos]
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]
    all_goals norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
    all_goals nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  rw [h18]
  all_goals norm_num [Real.sq_sqrt]
  all_goals nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]