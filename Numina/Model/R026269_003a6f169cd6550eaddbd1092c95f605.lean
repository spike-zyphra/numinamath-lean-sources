import Mathlib

open Real Set
open scoped Real

theorem algebra_279832 (f : ℝ → ℝ) (hf : f = λ x => sin x * sin (2 * x)) :
    IsGreatest (image f {x | x ∈ Ioo 0 (π / 2)}) (4 * sqrt 3 / 9) := by
  constructor
  · -- Show that 4 * sqrt 3 / 9 is in the image of f over (0, π / 2)
    use Real.arcsin (Real.sqrt 6 / 3)
    constructor
    · -- Show that arcsin (sqrt 6 / 3) is in (0, π / 2)
      have h1 : Real.sqrt 6 / 3 > 0 := by
        have h2 : Real.sqrt 6 > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        linarith
      have h3 : Real.sqrt 6 / 3 < 1 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      have h4 : Real.arcsin (Real.sqrt 6 / 3) > 0 := by
        apply Real.arcsin_pos.mpr
        linarith
      have h5 : Real.arcsin (Real.sqrt 6 / 3) < Real.pi / 2 := by
        apply (Real.arcsin_lt_pi_div_two).mpr
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      exact ⟨by linarith, by linarith⟩
    · -- Show that f (arcsin (sqrt 6 / 3)) = 4 * sqrt 3 / 9
      have h1 : Real.sin (Real.arcsin (Real.sqrt 6 / 3)) = Real.sqrt 6 / 3 := by
        apply Real.sin_arcsin
        · -- Show sqrt 6 / 3 >= -1
          have h2 : Real.sqrt 6 ≥ 0 := Real.sqrt_nonneg 6
          nlinarith
        · -- Show sqrt 6 / 3 <= 1
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      have h2 : Real.cos (Real.arcsin (Real.sqrt 6 / 3)) = Real.sqrt 3 / 3 := by
        have h1 : Real.cos (Real.arcsin (Real.sqrt 6 / 3)) = Real.sqrt (1 - (Real.sqrt 6 / 3) ^ 2) := by
          rw [Real.cos_arcsin]
        rw [h1]
        have h5 : 1 - (Real.sqrt 6 / 3) ^ 2 = (1 / 3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
        rw [h5]
        have h6 : Real.sqrt ((1 / 3 : ℝ)) = Real.sqrt 3 / 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h6]
      have h3 : sin (2 * (Real.arcsin (Real.sqrt 6 / 3))) = 2 * Real.sqrt 6 / 3 * Real.sqrt 3 / 3 := by
        rw [sin_two_mul]
        rw [h1, h2]
        all_goals linarith
      rw [hf]
      simp only
      rw [h1, h3]
      have h8 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
        calc
          Real.sqrt 6 * Real.sqrt 2 = Real.sqrt (6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 12 := by norm_num
          _ = Real.sqrt (4 * 3) := by norm_num
          _ = Real.sqrt 4 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
          _ = (2 : ℝ) * Real.sqrt 3 := by
            have h4sqrt4 : Real.sqrt 4 = (2 : ℝ) := by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [h4sqrt4]
            all_goals linarith
      have h9 : Real.sqrt 6 * Real.sqrt 3 = (3 : ℝ) * Real.sqrt 2 := by
        calc
          Real.sqrt 6 * Real.sqrt 3 = Real.sqrt (6 * 3) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 18 := by norm_num
          _ = Real.sqrt (9 * 2) := by norm_num
          _ = Real.sqrt 9 * Real.sqrt 2 := by rw [Real.sqrt_mul (by norm_num)]
          _ = (3 : ℝ) * Real.sqrt 2 := by
            have h4sqrt9 : Real.sqrt 9 = (3 : ℝ) := by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [h4sqrt9]
      nlinarith [h8, Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 6, sq_nonneg (Real.sqrt 6 - Real.sqrt 3 * 2)]
  · -- Show that 4 * sqrt 3 / 9 is greatest
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : 0 < x := by
      have h1 : x ∈ Ioo (0 : ℝ) (Real.pi / 2) := hx
      exact h1.1
    have hx2 : x < Real.pi / 2 := by
      have h1 : x ∈ Ioo (0 : ℝ) (Real.pi / 2) := hx
      exact h1.2
    have hx3 : 0 < Real.sin x := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have hx4 : 0 < Real.cos x := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith
      linarith
    rw [hf] at hfx
    simp at hfx
    have h1 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h1] at hfx
    nlinarith [ sq_nonneg (Real.sin x ^ 2 - 2 / 3),
              sq_nonneg (Real.sin x * Real.cos x - Real.sqrt 3 / 3),
              sq_nonneg (Real.sin x - Real.sqrt 6 / 3),
              sq_nonneg (Real.cos x - Real.sqrt 3 / 3),
              Real.sin_sq_add_cos_sq x, mul_nonneg (show 0 ≤ Real.sin x by linarith) (show 0 ≤ Real.cos x by linarith), 
              mul_pos (show (0 : ℝ) < Real.sin x by linarith) (show (0 : ℝ) < Real.cos x by linarith), 
              Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
              sq_nonneg (Real.sin x ^ 2 - 2 / 3) ]