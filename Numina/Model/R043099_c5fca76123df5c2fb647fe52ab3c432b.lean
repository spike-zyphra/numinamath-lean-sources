import Mathlib

open Real

theorem calculus_170335 :
  {t : ℝ | t > 0} =
  {t : ℝ | ∃ (T : ℝ) (R : ℝ),
    T > 0 ∧ R > 0 ∧
    
    -- 基于开普勒第三定律
    -- 退化椭圆的平均距离为 R/2
    -- T²/Tₑ² = R³/(R/2)³ = R³/(R³/8) = 8
    -- 因此 Tₑ = T/√8
    -- 坠落时间为周期的一半
    
    t = (T * sqrt (1/8) / 2) ∧
    
    -- 代入实际数据：T = 365.25天
    (T = 365.25 → abs (t - 64.5) < 0.1)} := by 
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume t > 0, prove the existence 
    intro ht
    use 4 * sqrt 2 * t, 2
    constructor
    · -- Show T > 0 
      have h1 : sqrt 2 > 0 := by 
        positivity
      nlinarith [ht, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0)]
    constructor
    · -- Show R > 0 
      norm_num
    constructor 
    · -- Show t = (T * sqrt (1 / 8) / 2)
      have h3 : sqrt (1 / 8) = 1 / (2 * sqrt 2) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num [mul_add, mul_comm]
      rw [h3]
      field_simp
      <;> ring_nf <;> norm_num
    · -- Show implication: T = 365.25 → abs (t - 64.5) < 0.1 
      intro hT 
      have hT' : 4 * sqrt 2 * t = (365.25 : ℝ) := by 
        linarith [hT]
      have ht' : t = (365.25 : ℝ) / (4 * sqrt 2) := by 
        field_simp at hT' ⊢
        linarith
      rw [ht']
      have h4 : abs ((365.25 / (4 * sqrt 2) : ℝ) - (64.5 : ℝ)) < 0.1 := by
        have h5 : sqrt 2 > 0 := by positivity
        have h6 : sqrt 2 < 2 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h7 : (365.25 / (4 * sqrt 2) : ℝ) - (64.5 : ℝ) > -0.1 := by 
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < sqrt 2 by positivity), Real.sqrt_nonneg (2 : ℝ)]
        have h8 : (365.25 / (4 * sqrt 2) : ℝ) - (64.5 : ℝ) < 0.1 := by 
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < sqrt 2 by positivity), Real.sqrt_nonneg (2 : ℝ)]
        apply abs_lt.mpr
        constructor <;> linarith 
      simpa using h4 
  · -- Assume the right side, prove left side
    intro h
    rcases h with ⟨T, R, hT, hR, ht_eq, himp⟩ 
    have ht_pos : t > 0 := by 
      by_contra h
      push_neg at h 
      have h12 : T * sqrt (1 / 8) / 2 ≤ (0 : ℝ) := by 
        nlinarith [ht_eq, h] 
      have h4 : sqrt (1 / 8) > 0 := by 
        positivity 
      nlinarith 
    linarith [ht_pos]