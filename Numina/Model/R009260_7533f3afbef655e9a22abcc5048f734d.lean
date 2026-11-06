import Mathlib

theorem algebra_277724 (x : ℝ) : 3 * x ^ 3 - ⌊x⌋ = 3 ↔ x = (4 / 3) ^ ((1 : ℝ) / 3) := by
  constructor
  · -- Assume 3 * x ^ 3 - ⌊x⌋ = 3, prove x = (4 / 3) ^ ((1 : ℝ) / 3)
    intro h_eq
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
    have hn2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h_eq2 : 3 * x ^ 3 - (n : ℝ) = 3 := by
      simpa using h_eq
    have h_eq3 : 3 * x ^ 3 = 3 + (n : ℝ) := by
      linarith
    have h_eq4 : x ^ 3 = 1 + (n : ℝ) / 3 := by
      nlinarith
    have h1 : n ≤ 1 := by
      by_contra h
      push_neg at h
      have h2 : n ≥ 2 := by omega
      have h3 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h2
      nlinarith [sq_nonneg (x ^ 2 - (2 : ℝ)), sq_nonneg (x - (2 : ℝ)), sq_nonneg (x - (1 : ℝ)), sq_nonneg (x - (4 / 3 : ℝ)), h_eq3, hn1, hn2, h3]
    have h2 : n ≥ 1 := by
      by_contra h
      push_neg at h
      have h3 : n ≤ 0 := by omega
      have h4 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h3
      nlinarith [sq_nonneg (x ^ 2 - (1 : ℝ)), sq_nonneg (x - (1 : ℝ)), sq_nonneg (x - (0 : ℝ)), sq_nonneg (x - (4 / 3 : ℝ)), h_eq3, hn1, hn2, h4]
    have hn : n = 1 := by omega
    have h5 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast hn
    have hx3 : x ^ 3 = (4 / 3 : ℝ) := by
      nlinarith [h_eq3, h5]
    have hx : x = (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h1 : x ^ 3 = (4 / 3 : ℝ) := hx3
      have h2 : x = (x ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h2, h1]
      all_goals norm_num
    exact hx
  · -- Assume x = (4 / 3) ^ ((1 : ℝ) / 3), prove 3 * x ^ 3 - ⌊x⌋ = 3
    intro h_eq
    have hx3 : x ^ 3 = (4 / 3 : ℝ) := by
      rw [h_eq]
      have h1 : ((4 / 3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith
    have hn1 : ⌊x⌋ = 1 := by
      have h1 : 1 < x := by
        rw [h_eq]
        have h : ((4 / 3 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) > (1 : ℝ) := by
          have h1 : (1 : ℝ) < (4 / 3 : ℝ) := by norm_num
          have h2 : (1 : ℝ) ^ ((1 : ℝ) / 3) = (1 : ℝ) := by
            simp
          have h3 : ((4 / 3 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) > (1 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            · norm_num
            · linarith
            · norm_num
          linarith [h2, h3]
        linarith
      have h2 : x < (2 : ℝ) := by
        rw [h_eq]
        have h : ((4 / 3 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) < (2 : ℝ) := by
          have h1 : (4 / 3 : ℝ) < (8 : ℝ) := by norm_num
          have h2 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
            have h1 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
              rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
              simp [Real.rpow_mul]
            linarith
          have h3 : ((4 / 3 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) < (8 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            · linarith
            · linarith
            · norm_num
          linarith [h2, h3]
        linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    have h_eq2 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast hn1
    have h_eq3 : 3 * x ^ 3 = 4 := by
      nlinarith [hx3]
    linarith [h_eq3, h_eq2]