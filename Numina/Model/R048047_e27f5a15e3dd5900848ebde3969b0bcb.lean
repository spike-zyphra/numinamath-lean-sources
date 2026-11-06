import Mathlib

open Real Set

theorem algebra_233666 :
    {x : ℝ | (4 : ℝ)^x + 17/64 ≥ 0 ∧ 2 * (4 : ℝ)^x - 7/64 ≥ 0 ∧ (4 : ℝ)^x - 1/16 ≥ 0 ∧
    Real.sqrt (4^x + 17/64) - Real.sqrt (2 * 4^x - 7/64) = Real.sqrt (4^x - 1/16)} = 
    {-3/2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ∈ left side, prove x = -3/2
    intro h
    rcases h with ⟨h1, h2, h3, heq⟩
    have h4 : (4 : ℝ) ^ x ≥ 0 := by positivity
    have eq1 : Real.sqrt ( (4: ℝ) ^ x + 17/64 ) = Real.sqrt (2 * (4: ℝ) ^ x - 7/64) + Real.sqrt ( (4: ℝ) ^ x - 1/16 ) := by
      linarith
    have eq2 : Real.sqrt ( (4: ℝ) ^ x + 17/64 ) ^ 2 = (Real.sqrt (2 * (4: ℝ) ^ x - 7/64) + Real.sqrt ( (4: ℝ) ^ x - 1/16 ) ) ^ 2 := by
      rw [eq1]
    have h5 : Real.sqrt ( (4: ℝ) ^ x + 17/64 ) ^ 2 = (4 : ℝ) ^ x + 17/64 := by
      apply Real.sq_sqrt
      linarith
    have eq3 : (Real.sqrt (2 * (4: ℝ) ^ x - 7/64) + Real.sqrt ( (4: ℝ) ^ x - 1/16 ) ) ^ 2 =
      Real.sqrt (2 * (4: ℝ) ^ x - 7/64) ^ 2 + Real.sqrt ( (4: ℝ) ^ x - 1/16 ) ^ 2 + 2 * (Real.sqrt (2 * (4: ℝ) ^ x - 7/64) * Real.sqrt ( (4: ℝ) ^ x - 1/16 ) ) := by ring
    rw [eq3] at eq2
    have h8 : Real.sqrt (2 * (4: ℝ) ^ x - 7/64) ^ 2 = 2 * (4: ℝ) ^ x - 7/64 := by
      apply Real.sq_sqrt
      nlinarith
    have h9 : Real.sqrt ( (4: ℝ) ^ x - 1/16 ) ^ 2 = (4: ℝ) ^ x - 1/16 := by
      apply Real.sq_sqrt
      nlinarith
    rw [h5, h8, h9] at eq2
    have h10 : (4 : ℝ) ^ x = 1/8 := by
      nlinarith [Real.sqrt_nonneg (2 * (4: ℝ) ^ x - 7/64), Real.sqrt_nonneg ( (4: ℝ) ^ x - 1/16 ), mul_nonneg (Real.sqrt_nonneg (2 * (4: ℝ) ^ x - 7/64)) (Real.sqrt_nonneg ( (4: ℝ) ^ x - 1/16 ) ) ]
    have h11 : (4 : ℝ) ^ x = 1/8 := h10
    have h12 : x = -3/2 := by
      have eq3 : (4 : ℝ) ^ x = 1/8 := h11
      have eq4 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x : ℝ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        ring
        all_goals linarith
      have eq5 : (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) := by
        norm_num
      rw [eq4] at eq3
      rw [eq5] at eq3
      have eq6 : 2 * x = -3 := by
        apply_fun (Real.logb (2 : ℝ)) at eq3
        have h14 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 * x : ℝ)) = (2 * x : ℝ) := by
          rw [Real.logb_rpow]
          all_goals linarith
        have h15 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (-3 : ℝ)) = (-3 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals linarith
        rw [h14, h15] at eq3
        nlinarith
      linarith
    linarith
  · -- Assume x = -3/2 prove x ∈ set
    intro h
    rw [h]
    constructor
    · -- Show (4 : ℝ)^(-3/2) + 17/64 ≥ 0
      have h10 : (4 : ℝ) ^ (-3 / 2 : ℝ) = 1/8 := by
        have h11 : (4 : ℝ) ^ (-3 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) := by
          norm_num
        rw [h11]
        have h12 : ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals linarith
        rw [h12]
        have h13 : (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) = (1 / 8 : ℝ) := by
          norm_num
        linarith
      nlinarith
    constructor
    · -- Show 2 * (4 : ℝ)^(-3/2) - 7/64 ≥ 0
      have h10 : (4 : ℝ) ^ (-3 / 2 : ℝ) = 1/8 := by
        have h11 : (4 : ℝ) ^ (-3 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) := by
          norm_num
        rw [h11]
        have h12 : ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals linarith
        rw [h12]
        have h13 : (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) = (1 / 8 : ℝ) := by
          norm_num
        linarith
      nlinarith
    constructor
    · -- Show (4 : ℝ)^(-3/2) - 1/16 ≥ 0
      have h10 : (4 : ℝ) ^ (-3 / 2 : ℝ) = 1/8 := by
        have h11 : (4 : ℝ) ^ (-3 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) := by
          norm_num
        rw [h11]
        have h12 : ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals linarith
        rw [h12]
        have h13 : (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) = (1 / 8 : ℝ) := by
          norm_num
        linarith
      nlinarith
    · -- Show sqrt(4^(-3/2)+17/64) - sqrt(2*4^(-3/2)-7/64) = sqrt(4^(-3/2)-1/16)
      have h10 : (4 : ℝ) ^ (-3 / 2 : ℝ) = 1/8 := by
        have h11 : (4 : ℝ) ^ (-3 / 2 : ℝ) = ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) := by
          norm_num
        rw [h11]
        have h12 : ((2 : ℝ) ^ (2 : ℝ)) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) := by
          rw [← Real.rpow_mul]
          ring
          all_goals linarith
        rw [h12]
        have h13 : (2 : ℝ) ^ (2 * (-3 / 2) : ℝ) = (1 / 8 : ℝ) := by
          norm_num
        linarith
      rw [h10]
      have h14 : Real.sqrt (1/8 + 17/64 : ℝ) = 5/8 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h15 : Real.sqrt (2 * (1/8 : ℝ) - 7/64) = 3/8 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      have h16 : Real.sqrt (1/8 - 1/16 : ℝ) = 1/4 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h14, h15, h16]
      all_goals linarith