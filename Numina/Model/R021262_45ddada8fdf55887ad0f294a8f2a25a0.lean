import Mathlib

theorem algebra_129706 (x : ℝ) : x^3 - ⌊x⌋ = 3 ↔ x = 4 ^ ((1 : ℝ) / 3) := by
  constructor
  · -- Assume x^3 - ⌊x⌋ = 3, prove x = 4^(1/3)
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have eq1 : x^3 = (⌊x⌋ + 3 : ℝ) := by
      have eq2 : x^3 - (⌊x⌋ : ℝ) = 3 := by
        simpa using h
      linarith
    have h3 : ⌊x⌋ ≤ 1 := by
      by_contra h3
      push_neg at h3
      have h4 : ⌊x⌋ ≥ 2 := by omega
      have h5 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
        exact_mod_cast h4
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 - 5)]
    have h3' : ⌊x⌋ ≥ 1 := by
      by_contra h3'
      push_neg at h3'
      have h4 : ⌊x⌋ ≤ 0 := by omega
      have h5 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by
        exact_mod_cast h4
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
    have h3'' : ⌊x⌋ = 1 := by omega
    have h4 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h3''
    -- From Equation
    have eq2 : x^3 = (4 : ℝ) := by
      rw [h4] at eq1
      nlinarith
    have h5 : x = (4 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h6 : x^3 = (4 : ℝ) := eq2
      have h7 : x = ((x ^ 3) ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals nlinarith
      rw [h6] at h7
      linarith
    exact h5
  · -- Assume x = 4 ^ (1 / 3), prove x^3 - ⌊x⌋ = 3
    intro h
    have h1 : x = (4 : ℝ) ^ ((1 : ℝ) / 3) := by
      linarith
    have h2 : ⌊x⌋ = 1 := by
      have h3 : 1 ≤ x := by
        have h4 : x ^ 3 = (4 : ℝ) := by
          have h5 : x = (4 : ℝ) ^ ((1 : ℝ) / 3) := h1
          rw [h5]
          have h6 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals nlinarith
          linarith
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h4 : x < (2 : ℝ) := by
        have h5 : x^3 = (4 : ℝ) := by
          have h6 : x = (4 : ℝ) ^ ((1 : ℝ) / 3) := h1
          rw [h6]
          have h7 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals nlinarith
          linarith
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_nonneg (x ^ 2 - 4)]
      have h5 : ⌊x⌋ = 1 := by
        rw [Int.floor_eq_iff
        ]
        constructor <;> (try norm_num) <;> nlinarith
      exact h5
    -- From Equation
    have h6 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h2
    -- Equation
    have eq1 : x^3 - (⌊x⌋ : ℝ) = 3 := by
      rw [h6]
      have h7 : x ^ 3 = (4 : ℝ) := by
        have h8 : x = (4 : ℝ) ^ ((1 : ℝ) / 3) := h1
        rw [h8]
        have h9 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals nlinarith
        nlinarith
      nlinarith
    linarith