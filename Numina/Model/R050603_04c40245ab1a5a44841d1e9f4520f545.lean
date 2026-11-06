import Mathlib

open Real Set
open scoped Real

theorem algebra_198750 : IsGreatest {x | ∃ t : ℝ, x = sin t + sqrt 2 * cos t} (sqrt 3) := by
  constructor
  · -- First, we need to show that sqrt(3) is indeed achievable by some real number t.
    use Real.pi / 2 - Real.arccos (1 / Real.sqrt 3)
    have h1 : cos (Real.arccos (1 / Real.sqrt 3)) = 1 / Real.sqrt 3 := by
      apply Real.cos_arccos
      · -- Show that -1 ≤ 1 / Real.sqrt 3
        have h1 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
        have h2 : 1 / Real.sqrt 3 ≥ -1 := by 
          have h3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
          have h4 : 1 / Real.sqrt 3 > 0 := by positivity 
          linarith 
        linarith 
      · -- Show that 1 / Real.sqrt 3 ≤ 1
        have h2 : Real.sqrt 3 ≥ 1 := by 
          have h3 : Real.sqrt 1 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num) 
          have h4 : Real.sqrt 1 = 1 := Real.sqrt_one 
          linarith [h3, h4] 
        have h5 : 1 / Real.sqrt 3 ≤ 1 := by 
          apply (div_le_one (by positivity)).mpr 
          linarith 
        linarith 
    have h2 : sin (Real.arccos (1 / Real.sqrt 3)) = Real.sqrt (1 - (1 / Real.sqrt 3) ^ 2) := by 
      rw [Real.sin_arccos] 
    have h3 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by 
      calc 
        (1 / Real.sqrt 3) ^ 2 = 1 ^ 2 / (Real.sqrt 3) ^ 2 := by field_simp 
        _ = 1 / (Real.sqrt 3) ^ 2 := by ring 
        _ = 1 / 3 := by rw [Real.sq_sqrt]; positivity 
    have h4 : Real.sqrt (1 - (1 / Real.sqrt 3) ^ 2) = Real.sqrt (2 / 3) := by 
      rw [h3] 
      ring_nf 
    rw [show sin (Real.pi / 2 - Real.arccos (1 / Real.sqrt 3)) = cos (Real.arccos (1 / Real.sqrt 3)) by 
      rw [Real.sin_pi_div_two_sub] 
    ]
    rw [show cos (Real.pi / 2 - Real.arccos (1 / Real.sqrt 3)) = sin (Real.arccos (1 / Real.sqrt 3)) by 
      rw [Real.cos_pi_div_two_sub] 
    ]
    rw [h1, h2, h4] 
    have h5 : Real.sqrt (2 / 3) = Real.sqrt 2 / Real.sqrt 3 := by 
      field_simp [Real.sqrt_div] 
      all_goals norm_num 
    rw [h5] 
    have h6 : 1 / Real.sqrt 3 + Real.sqrt 2 * (Real.sqrt 2 / Real.sqrt 3) = Real.sqrt 3 := by 
      have h7 : Real.sqrt 2 * (Real.sqrt 2 / Real.sqrt 3) = 2 / Real.sqrt 3 := by 
        field_simp 
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      rw [h7] 
      have h8 : 1 / Real.sqrt 3 + 2 / Real.sqrt 3 = 3 / Real.sqrt 3 := by 
        ring 
      rw [h8] 
      have h9 : 3 / Real.sqrt 3 = Real.sqrt 3 := by 
        have h10 : Real.sqrt 3 > 0 := by positivity 
        field_simp 
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith [h9] 
    linarith [h6] 
  · -- Now, we need to prove that sqrt(3) is the maximum.
    intro x hx 
    rcases hx with ⟨t, ht⟩ 
    have h2 : sin t + Real.sqrt 2 * cos t ≤ Real.sqrt 3 := by 
      have h3 : (sin t + Real.sqrt 2 * cos t) ^ 2 ≤ 3 := by 
        nlinarith [sq_nonneg (sin t * Real.sqrt 2 - cos t), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sin_sq_add_cos_sq t] 
      have h4 : Real.sqrt 3 ≥ 0 := by positivity 
      have h5 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) 
      nlinarith [h3, Real.sqrt_nonneg (sin t + Real.sqrt 2 * cos t), Real.sqrt_nonneg 3, h5, sq_nonneg (sin t + Real.sqrt 2 * cos t - Real.sqrt 3)]
    linarith [ht, h2]