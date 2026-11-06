import Mathlib

open Real

theorem inequalities_260938 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sqrt (a * b) ≤ 2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ∧
    2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ≤ (a + b) / 2 ∧
    (sqrt (a * b) = 2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ↔
      a = b) ∧ (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) = (a + b) / 2 ↔
      a = b) := by
  have h1 : sqrt (a * b) ≤ 2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) := by
    have h2 : 0 < a * b := mul_pos ha hb
    have h3 : sqrt (a * b) ≥ 0 := by positivity
    have h4 : (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ) ≥ 0 := by
      apply div_nonneg
      · -- Numerator is non-negative
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb]
      · -- Denominator is positive
        positivity
    have h5 : (sqrt (a * b)) ^ 2 ≤ (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ) ^ 2 := by
      have h6 : (sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by nlinarith)
      have h10 : (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ) ^ 2 = (2 * (a^2 + 3 * a * b + b^2)) ^ 2 / (5 * (a + b)) ^ 2 := by
        field_simp
      rw [h6, h10]
      apply (le_div_iff₀ (by positivity : 0 < (5 * (a + b) ) ^ 2)).mpr
      nlinarith [ sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_nonneg (a^2 - b^2), sq_nonneg (a * (a - b) ), sq_nonneg (b * (a - b) ), mul_pos ha hb
      ]
    nlinarith [ Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (a * b), h3, show (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b))) ≥ 0 by positivity ]
  have h2 : 2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ≤ (a + b) / 2 := by
    have h11 : 0 < 5 * (a + b) := by positivity
    have h12 : 0 < (2 : ℝ) := by positivity
    have h13 : 4 * (a^2 + 3 * a * b + b^2) ≤ 5 * (a + b)^2 := by
      nlinarith [ sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb
      ]
    have h14 : 2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ≤ (a + b) / 2 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [ h13 ]
    linarith
  have h3 : (sqrt (a * b) = 2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ↔ a = b) := by
    constructor
    · -- Assume sqrt (a * b) = 2 * (a ^ 2 + 3 * a * b + b ^ 2) / (5 * (a + b))
      intro h_eq
      have h4 : (sqrt (a * b)) ^ 2 = (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ) ^ 2 := by
        rw [h_eq]
      have h5 : (sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
      have h7 : (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ) ^ 2 = (2 * (a^2 + 3 * a * b + b^2)) ^ 2 / (5 * (a + b)) ^ 2 := by
        field_simp
      rw [h5, h7] at h4
      have h9 : (a - b) ^ 2 = 0 := by
        field_simp at h4
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb
        ]
      have h10 : a - b = 0 := by
        apply pow_eq_zero 
        exact h9
      linarith
      all_goals linarith
    · -- Assume a = b
      intro h12
      rw [h12]
      field_simp
      <;> nlinarith [ Real.sqrt_nonneg (a * a), Real.sq_sqrt (show 0 ≤ (a * a : ℝ) by positivity) ]
  have h4 : (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) = (a + b) / 2 ↔ a = b) := by
    constructor
    · -- Assume 2 * (a ^ 2 + 3 * a * b + b ^ 2) / (5 * (a + b)) = (a + b) / 2
      intro h5
      have h6 : 4 * (a^2 + 3 * a * b + b^2) = 5 * (a + b) ^ 2 := by
        have h5' : 5 * (a + b) > 0 := by positivity
        have h8 : (2 : ℝ) > 0 := by norm_num
        have h7 : (2 * (a^2 + 3 * a * b + b^2) / (5 * (a + b)) ) = (a + b) / 2 := h5
        field_simp [(show 0 < 5 * (a + b) from by positivity), show 0 < (2 : ℝ) by norm_num] at h7 ⊢
        nlinarith [ h7 ]
      have h13 : (a - b) ^ 2 = 0 := by
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb
        ]
      have h14 : a - b = 0 := by
        apply pow_eq_zero 
        exact h13
      linarith
    · -- Assume a = b
      intro h5
      rw [h5]
      field_simp
      <;> ring_nf
  exact ⟨h1, h2, h3, h4⟩