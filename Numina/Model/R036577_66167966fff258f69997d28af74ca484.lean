import Mathlib


theorem algebra_172760 (x : ℝ) :
    3 * x ^ 3 - ⌊x⌋ = 3 ↔ x = (4 / 3) ^ ((1 : ℝ) / 3) := by
  constructor
  · -- Assume 3 * x ^ 3 - ⌊x⌋ = 3, prove x = (4 / 3) ^ ((1 : ℝ) / 3)
    intro h
    have eq1 : 3 * x ^ 3 = 3 + (⌊x⌋ : ℝ) := by
      have h1 : (3 * x ^ 3 - ⌊x⌋ : ℝ) = 3 := by
        linarith
      nlinarith
    have h10 : ⌊x⌋ ≤ (x : ℝ) := by
      exact Int.floor_le x
    have h11 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h2 : ⌊x⌋ = 1 := by
      have h3 : ⌊x⌋ ≤ 1 := by
        by_contra h3
        push_neg at h3
        have h4 : ⌊x⌋ ≥ 2 := by omega
        have h5 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h4
        nlinarith [sq_nonneg (x - 1.58 : ℝ), sq_nonneg (x ^ 2 : ℝ), sq_nonneg ((x): ℝ), sq_nonneg ((x) - (1 : ℝ)), sq_nonneg ((x) - (2 : ℝ)), sq_nonneg ((⌊x⌋ : ℝ) - (2 : ℝ))]
      have h4 : ⌊x⌋ ≥ 1 := by
        by_contra h4
        push_neg at h4
        have h5 : ⌊x⌋ ≤ 0 := by omega
        have h6 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h5
        nlinarith [sq_nonneg (x - (0 : ℝ) : ℝ), sq_nonneg (x ^ 2 : ℝ), sq_nonneg ((x): ℝ), sq_nonneg ((x) + (1 : ℝ)), sq_nonneg ((x) - (0 : ℝ)), sq_nonneg ((⌊x⌋ : ℝ) - (0 : ℝ))]
      omega
    have h3 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h2
    have h40 : 3 * x ^ 3 = 4 := by
      linarith
    have h50 : x ^ 3 = 4 / 3 := by
      nlinarith
    have h80 : x = (4 / 3) ^ ((1 : ℝ) / 3) := by
      have h90 : x ^ 3 = (4 / 3 : ℝ) := h50
      have h100 : x = ((x ^ 3) : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x), sq_nonneg (x ^ 2 - 1)]
      rw [show (x ^ 3 : ℝ) = (4 / 3 : ℝ) by linarith [h90]] at h100
      linarith
    exact h80
  · -- Assume x = (4 / 3) ^ ((1 : ℝ) / 3), prove 3 * x ^ 3 - ⌊x⌋ = 3
    intro h
    have h1 : x ^ 3 = (4 / 3 : ℝ) := by
      rw [show x = (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) by linarith [h]]
      have h2 : ((4 / 3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          norm_num
      linarith
    have h3 : ⌊x⌋ = 1 := by
      have h40 : 1 < x := by
        have h100 : x = (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by linarith [h]
        rw [h100]
        have h101 : (1 : ℝ) < (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by
          have h102 : (1 : ℝ) < (4 / 3 : ℝ) := by norm_num
          have h103 : (1 : ℝ) ^ ((1 : ℝ) / 3) < (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            all_goals
              norm_num
          have h104 : (1 : ℝ) ^ ((1 : ℝ) / 3) = (1 : ℝ) := by
            simp
          nlinarith
        linarith
      have h41 : x < (2 : ℝ) := by
        have h100 : x = (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) := by linarith [h]
        rw [h100]
        have h101 : (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) < (2 : ℝ) := by
          have h102 : (4 / 3 : ℝ) < (8 : ℝ) := by norm_num
          have h103 : (4 / 3 : ℝ) ^ ((1 : ℝ) / 3) < (8 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            all_goals
              norm_num
          have h104 : (8 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
            have h105 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
            rw [h105]
            have h106 : ((2 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (2 : ℝ) := by
              rw [← Real.rpow_mul]
              norm_num
              all_goals
                norm_num
            linarith
          nlinarith
        linarith
      have h42 : 1 < x := h40
      have h43 : x < (2 : ℝ) := h41
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith
    have h400 : (3 * x ^ 3 - ⌊x⌋ : ℝ) = 3 := by
      have h200 : (⌊x⌋ : ℝ) = 1 := by
        exact_mod_cast (show ⌊x⌋ = 1 by linarith [h3])
      nlinarith [h1, h200]
    linarith