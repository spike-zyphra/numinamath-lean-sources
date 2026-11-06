import Mathlib

open Real
open scoped BigOperators

theorem algebra_11743 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) :
  1 - sqrt 2 / 2 ≤ (a^3 + b^3 + c^3) / (c * (a + b + c)^2) ∧
  (a^3 + b^3 + c^3) / (c * (a + b + c)^2) < 1 / 2 := by
  have h4 : 0 < c := by linarith
  have h5 : a + b + c > 0 := by linarith
  have h6 : a + b ≤ c * Real.sqrt 2 := by
    have h7 : (a + b) ^ 2 ≤ 2 * (a^2 + b^2) := by
      nlinarith [sq_nonneg (a - b)]
    have h8 : (a + b) ^ 2 ≤ 2 * c^2 := by
      have eq1 : a^2 + b^2 = c^2 := h₃
      nlinarith [h7, eq1]
    have h9 : Real.sqrt ((a + b) ^ 2) = a + b := by
      rw [Real.sqrt_sq (by positivity)]
    have h10 : Real.sqrt (2 * c ^ 2) = Real.sqrt 2 * c := by
      have hc : c ≥ 0 := by linarith
      have h2 : 2 * c ^ 2 = 2 * (c ^ 2) := by ring
      rw [h2]
      have h3 : Real.sqrt (2 * (c ^ 2)) = Real.sqrt 2 * Real.sqrt (c ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      have h4 : Real.sqrt (c ^ 2) = c := by
        rw [Real.sqrt_sq (by linarith)]
      rw [h3, h4]
      all_goals linarith
    have h11 : Real.sqrt ((a + b) ^ 2) ≤ Real.sqrt (2 * c ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [h8]
    linarith [h9, h11, h10]
  constructor
  · -- Prove 1 - sqrt 2 / 2 ≤ (a^3 + b^3 + c^3) / (c * (a + b + c)^2)
    have h18 : 0 < c * (a + b + c) ^2 := by positivity
    have h19 : (a^3 + b^3 + c^3) / (c * (a + b + c)^2) ≥ 1 - sqrt 2 / 2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      have h15 : (a^3 + b^3 + c^3) ≥ (1 - sqrt 2 / 2) * c * (a + b + c) ^2 := by
        have ha : a > 0 := h₀
        have hb : b > 0 := h₁
        have hc : c > 0 := h₂
        have h8 : a^2 + b^2 = c^2 := h₃
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c * Real.sqrt 2 / 2 * 2), sq_nonneg (c - (a + b) * Real.sqrt 2 / 2), sq_nonneg (a^2 + b^2 - c^2), 
          Real.sqrt_nonneg (2), sq_nonneg (a + b - c), sq_nonneg (a * b - c^2 / 2), sq_nonneg (c - a * Real.sqrt 2 / 2 - b * Real.sqrt 2 / 2), 
          Real.sqrt_nonneg (2), sq_nonneg ((a - b) * (a - b) ), sq_nonneg ((a + b - c) * (a + b - c)), 
          sq_nonneg ((a^2 + b^2) - c^2), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ (2: ℝ) by norm_num), 
          sq_nonneg ((Real.sqrt 2) ^2 - 2 ), mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
          mul_pos (show 0 < Real.sqrt 2 by positivity) (show 0 < Real.sqrt 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (2: ℝ) by norm_num), 
          Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num)
        ]
      linarith
    linarith
  · -- Prove (a^3 + b^3 + c^3) / (c * (a + b + c)^2) < 1 / 2
    apply (div_lt_iff₀ (by positivity)).mpr
    have h13 : a^3 + b^3 + c^3 < (1 / 2) * c * (a + b + c) ^2 := by
      have h14 : 0 < a * b := mul_pos h₀ h₁
      have h15 : 0 < c := h4
      nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₁, sq_pos_of_pos h₂,
        sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (a^2 + b^2 - c^2),
        sq_nonneg (a * b - (c ^2 / 2)), sq_nonneg ((a + b) ^2 - c^2), sq_nonneg (a + b - c),
        Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
        sq_nonneg (c^2 - a^2 - b^2), sq_nonneg ( (a + b) - c * Real.sqrt 2 / 2 )
      ]
    linarith