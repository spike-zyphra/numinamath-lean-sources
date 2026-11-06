import Mathlib

theorem algebra_305753 {x : ℝ} (hx : x > 0) :
    ⌊x⌋^2 = x * (x - ⌊x⌋) ↔ x = (Real.sqrt 5 + 1) / 2 := by
  constructor
  · -- Assume ⌊x⌋^2 = x * (x - ⌊x⌋), prove x = (√5 +1)/2
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x

    have h3 : ⌊x⌋ = 1 := by
      have h31 : ⌊x⌋ ≤ 1 := by
        by_contra h5
        push_neg at h5
        have h4 : ⌊x⌋ ≥ 2 := by
          omega
        have h5 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
          exact_mod_cast h4
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x - (Real.sqrt 5 + 1) / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), h1, h2, sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ : ℝ) - (Real.sqrt 5 + 1) / 2), Real.sqrt_nonneg 5]
      have h311 : ¬ (⌊x⌋ ≤ 0) := by 
        intro h312 
        have h4 : ⌊x⌋ ≤ 0 := by omega
        have h5 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h4
        by_cases h6 : ⌊x⌋ = 0
        · -- Case `⌊x⌋ = 0`.
          have h6' : (⌊x⌋ : ℝ) = (0 : ℝ) := by 
            exact_mod_cast h6
          rw [h6'] at h
          nlinarith
        · -- Case `⌊x⌋ ≠ 0`.
          have h7 : ⌊x⌋ ≤ -1 := by 
            omega 
          have h8 : ⌊x⌋ < 1 := by
            omega 
          have h8' : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by 
            exact_mod_cast h7 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x), sq_nonneg (x - 1), h]
      have h312 : ⌊x⌋ = 1 := by 
        omega 
      exact h312 
    have h4 : (⌊x⌋ : ℝ) = (1 : ℝ) := by 
      exact_mod_cast h3 
    have h5 : x ^ 2 - x - 1 = 0 := by 
      rw [h4] at h 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x - (Real.sqrt 5 + 1) / 2), Real.sqrt_nonneg 5, h1, h2] 
    nlinarith [sq_nonneg (x - (Real.sqrt 5 + 1) / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5, h5]

  intro h
  rw [h]
  have h1 : ⌊((Real.sqrt 5 + 1) / 2 : ℝ)⌋ = 1 := by 
    have h3 : 1 < (Real.sqrt 5 + 1) / 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5] 
    have h4 : (Real.sqrt 5 + 1) / 2 < (2 : ℝ) := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5] 
    rw [Int.floor_eq_iff] 
    constructor <;> (try norm_num) <;> nlinarith 
  rw [h1] 
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5, sq_nonneg ((Real.sqrt 5 + 1) / 2 - (1 : ℝ))]