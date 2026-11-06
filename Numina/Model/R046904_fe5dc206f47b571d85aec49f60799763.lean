import Mathlib

open Real Set

theorem algebra_599852:
  IsGreatest {y | ∃ x : ℝ, x ∈ Ioo 0 (π/2) ∧ y = 3 * cos x + 4 * sqrt (1 + sin x ^ 2)} (5 * sqrt 2) := by
  constructor
  · -- Show $5\sqrt{2}$ is in the image of $f$ over $(0, \frac{\pi}{2})$.
    use arcsin (Real.sqrt 7 / 5)
    constructor
    · -- Show arcsin (sqrt 7 / 5) ∈ Ioo 0 (π/2)
      constructor
      · -- Show 0 < arcsin (sqrt 7 / 5)
        have h1 : Real.sqrt 7 > 0 := by
          positivity
        have h2 : Real.sqrt 7 / 5 > 0 := by nlinarith [h1]
        have h8 : Real.arcsin (Real.sqrt 7 / 5) > 0 := by
          apply Real.arcsin_pos.2
          all_goals linarith
        linarith
      · -- Show arcsin (sqrt 7 / 5) < π/2
        have h1 : Real.sqrt 7 / 5 > 0 := by
          have h1 : Real.sqrt 7 > 0 := by
            positivity
          nlinarith [h1]
        have h4 : Real.sqrt 7 / 5 < 1 := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
        have h10 : Real.arcsin (Real.sqrt 7 / 5) < Real.pi / 2 := by
          apply Real.arcsin_lt_pi_div_two.mpr
          nlinarith [h4]
        linarith
    · -- Show 5 * sqrt 2 = 3 * cos (arcsin (sqrt 7 / 5)) + 4 * sqrt (1 + sin (arcsin (sqrt 7 / 5)) ^ 2)
      have h1 : Real.sin (Real.arcsin (Real.sqrt 7 / 5)) = Real.sqrt 7 / 5 := by
        apply Real.sin_arcsin
        · -- Show -1 ≤ sqrt 7 / 5
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
        all_goals
        · -- Show sqrt 7 / 5 ≤ 1
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
      have h10 : Real.cos (Real.arcsin (Real.sqrt 7 / 5)) = 3 * Real.sqrt 2 / 5 := by
        have h2 : Real.cos (Real.arcsin (Real.sqrt 7 / 5)) = Real.sqrt (1 - (Real.sqrt 7 / 5) ^ 2) := by
          rw [Real.cos_arcsin]
        rw [h2]
        have h3 : 1 - (Real.sqrt 7 / 5) ^ 2 = (18 / 25 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
        rw [h3]
        have h4 : Real.sqrt (18 / 25 : ℝ) = (3 * Real.sqrt 2 / 5 : ℝ) := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h4]
      have h30 : Real.sqrt (1 + (Real.sin (Real.arcsin (Real.sqrt 7 / 5)) ^ 2)) = (4 * Real.sqrt 2 / 5 : ℝ) := by
        have h25 : Real.sin (Real.arcsin (Real.sqrt 7 / 5)) = Real.sqrt 7 / 5 := by
          apply Real.sin_arcsin
          · -- Show -1 ≤ sqrt 7 / 5
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
          all_goals
          · -- Show sqrt 7 / 5 ≤ 1
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
        rw [h25]
        have h30 : (1 + (Real.sqrt 7 / 5) ^ 2) = (32 / 25 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg 7]
        rw [h30]
        have h32 : Real.sqrt (32 / 25 : ℝ) = (4 * Real.sqrt 2 / 5 : ℝ) := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h32]
      rw [h10, h30]
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  · -- Show $5\sqrt 2$ is the greatest element in the image.
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hx1⟩
    have h1 : 0 < x := hx0
    have h2 : x < Real.pi / 2 := hx1
    have h5 : Real.cos x > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have h7 : Real.sin x > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [h1, Real.pi_pos]
      · linarith [h2, Real.pi_pos]
    have h10 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2)) ≤ 5 * Real.sqrt 2 := by
      have h100 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2)) ^ 2 ≤ (50 : ℝ) := by
        have h1000 : (Real.cos x)^2 + (Real.sqrt (1 + Real.sin x ^ 2)) ^ 2 = 2 := by
          have h50 : (Real.sqrt (1 + Real.sin x ^ 2)) ^ 2 = 1 + Real.sin x ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          nlinarith [Real.sin_sq_add_cos_sq x]
        have h100 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2)) ^ 2 ≤ (3 ^ 2 + 4 ^ 2 : ℝ) * ((Real.cos x)^2 + (Real.sqrt (1 + Real.sin x ^ 2)) ^ 2) := by
          nlinarith [sq_nonneg (3 * Real.sqrt (1 + Real.sin x ^ 2) - 4 * Real.cos x)]
        rw [h1000] at h100
        nlinarith [Real.sin_sq_add_cos_sq x]
      have h14 : Real.sqrt (50) = 5 * Real.sqrt 2 := by
        calc
          Real.sqrt (50) = Real.sqrt (5^2 * 2) := by norm_num
          _ = (5) * Real.sqrt (2) := by
            rw [Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_sq (by norm_num)]
          _ = (5 * Real.sqrt 2) := by ring
      have h1000 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2)) ≤ Real.sqrt (50 : ℝ) := by
        have h1700 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2)) ≤ Real.sqrt (50 : ℝ) := by
          have h1000 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2)) ^ 2 ≤ (50 : ℝ) := h100
          have h1400 : (0 : ℝ) ≤ (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2) : ℝ) := by
            nlinarith [Real.sqrt_nonneg (1 + Real.sin x ^ 2), Real.sin_sq_add_cos_sq x]
          have h1500 : (3 * Real.cos x + 4 * Real.sqrt (1 + Real.sin x ^ 2) : ℝ) ≤ Real.sqrt (50 : ℝ) := by
            apply Real.le_sqrt_of_sq_le
            linarith
          linarith
        linarith
      nlinarith [Real.sqrt_nonneg (50 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (50 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    nlinarith