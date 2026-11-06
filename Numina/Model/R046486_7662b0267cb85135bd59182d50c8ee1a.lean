import Mathlib

theorem algebra_321262 (x y a : ℝ) (ha : 0 < a) (h : x^3 + y^3 = a^3) :
    0 < x + y ∧ x + y ≤ 4 ^ ((1 : ℝ) / 3) * a := by
  have h1 : 0 < x + y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (a - (x + y)), sq_nonneg (x - a), sq_nonneg (y - a), 
      mul_pos ha (show 0 < a by linarith)]
  have h2 : x + y ≤ (4 : ℝ) ^ ((1 : ℝ) / 3) * a := by
    have h3 : (x + y : ℝ) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg ((x + y) ^ 2 - (x ^ 2 + y ^ 2)), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - (x + y) ^ 2 / 4)]
    have h4 : (x + y) ^ 3 ≤ 4 * (a ^ 3) := by
      nlinarith [h, h3]
    have h9 : (x + y) ^ 3 ≤ 4 * (a ^ 3) := h4
    have h6 : (x + y) ≤ ((4 * (a ^ 3) ) : ℝ) ^ (1 / 3 : ℝ) := by
      have h7 : (( (x + y) ^ 3 ) ) ^ (1 / 3 : ℝ) = (x + y) := by
        have h9 : (x + y) ≥ 0 := by nlinarith
        have h8 : ( (x + y) ^ 3 ) ^ (1 / 3 : ℝ) = (x + y) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul]
          norm_num
          all_goals
          nlinarith
        linarith
      have h8 : ((4 * (a ^ 3) ) : ℝ) ^ (1 / 3 : ℝ) ≥ (x + y) := by
        have h10 : (( (x + y) ^ 3 ) ) ^ (1 / 3 : ℝ) = (x + y) := h7
        -- Show first ((x+y)^3)^(1/3) <= ((4*a^3))^(1/3)
        have h11 : (( (x + y) ^ 3 ) ) ^ (1 / 3 : ℝ) ≤ ((4 * (a ^ 3) ) : ℝ) ^ (1 / 3 : ℝ) := by
          apply Real.rpow_le_rpow
          have h12 : 0 ≤ (x + y : ℝ) ^ 3 := by
            have h13 : (x + y : ℝ) ≥ 0 := by
              linarith
            have h14 : (x + y : ℝ) ^ 3 ≥ 0 := by positivity
            linarith
          linarith
          all_goals
          nlinarith
          all_goals
          norm_num
          all_goals
          positivity
        nlinarith [h11, h10]
      nlinarith
      all_goals
      nlinarith
    have h7 : (( (4 * (a ^ 3) ) : ℝ) ^ (1 / 3 : ℝ) ) = (4 : ℝ) ^ (1 / 3 : ℝ) * a := by 
      have h10 : ((4 * (a ^ 3) : ℝ) ) ^ (1 / 3 : ℝ) = (4 : ℝ) ^ (1 / 3 : ℝ) * ((a ^ 3) ^ (1 / 3 : ℝ)) := by 
        rw [← Real.mul_rpow]
        all_goals
        positivity
      have h13 : (a ^ 3 : ℝ) ^ (1 / 3 : ℝ) = a := by
        rw [show (a ^ 3: ℝ) ^ (1 / 3: ℝ) = (a: ℝ) by
          have h11 : (a ^ 3: ℝ) ^ (1 / 3 : ℝ) = (a: ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul]
            norm_num
            all_goals
            positivity
          linarith
        ]
        all_goals
        linarith
      rw [h10, h13]
      <;> ring_nf <;> norm_num
      all_goals positivity
    nlinarith [h7, h6]
    all_goals
    nlinarith
  constructor
  · exact h1
  · exact h2