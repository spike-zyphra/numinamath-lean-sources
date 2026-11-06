import Mathlib
open Real
theorem algebra_610960 (f : ℝ → ℝ) (N : ℝ) (hf : f = fun x => (x - 1) / (x + 1)) (hN : N ≠ -1) : f (f N) = tan (15 * π / 180) ↔ N = -2 - √3:= by
  have h1 : f (f N) = -1 / N := by
    rw [hf]
    have hN1 : N + 1 ≠ 0 := by
      intro h
      apply hN
      linarith
    simp [hN1]
    field_simp [hN1]
    <;> ring
  have h2 : tan (15 * π / 180) = 2 - Real.sqrt 3 := by
    have h1 : 15 * π / 180 = π / 12 := by ring
    rw [h1]
    have h2 : tan (π / 12) = 2 - Real.sqrt 3 := by
      have h2 : tan (π / 12) = (tan (π / 4) - tan (π / 6)) / (1 + tan (π / 4) * tan (π / 6)) := by
        rw [show π / 12 = π / 4 - π / 6 by ring]
        rw [Real.tan_eq_sin_div_cos]
        rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
        have hsin : sin (π / 4 - π / 6) = sin (π / 4) * cos (π / 6) - cos (π / 4) * sin (π / 6) := by
          rw [Real.sin_sub]
        have hcos : cos (π / 4 - π / 6) = cos (π / 4) * cos (π / 6) + sin (π / 4) * sin (π / 6) := by
          rw [Real.cos_sub]
        rw [hsin, hcos]
        field_simp [Real.sin_pi_div_four, Real.cos_pi_div_four, Real.sin_pi_div_six, Real.cos_pi_div_six]
        <;> ring
      have h4 : tan (π / 4) = 1 := Real.tan_pi_div_four
      have h5 : tan (π / 6) = Real.sqrt 3 / 3 := by
        rw [Real.tan_eq_sin_div_cos]
        have h1 : sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
        have h2 : cos (π / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
        rw [h1, h2]
        field_simp
      rw [h2, h4, h5]
      field_simp [show 3 + Real.sqrt 3 ≠ 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact h2
  constructor
  · -- Assume f(f N) = tan 15°, prove N = -2 - √3
    intro h_eq
    rw [h1] at h_eq
    rw [h2] at h_eq
    have hN2 : N ≠ 0 := by
      by_contra h
      rw [h] at h_eq
      field_simp at h_eq
      all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have hN_eq : N = -2 - Real.sqrt 3 := by
      field_simp at h_eq
      have h3 : (2 - Real.sqrt 3) * N = -1 := by nlinarith
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      have h5 : (2 - Real.sqrt 3 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      -- Solving for N
      have h6 : N = -1 / (2 - Real.sqrt 3) := by
        field_simp [h5]
        linarith
      rw [h6]
      have h7 : -1 / (2 - Real.sqrt 3 : ℝ) = -2 - Real.sqrt 3 := by
        field_simp [show (2 - Real.sqrt 3 : ℝ) ≠ 0 by
          have h5 : (2 - Real.sqrt 3 : ℝ) ≠ 0 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          exact h5
        , Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
    exact hN_eq
  · -- Assume N = -2 - √3, prove f(f N) = tan 15°
    intro h_eq
    rw [h1, h2, h_eq]
    have h3 : (-2 - Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [show (-2 - Real.sqrt 3 : ℝ) ≠ 0 by exact h3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]