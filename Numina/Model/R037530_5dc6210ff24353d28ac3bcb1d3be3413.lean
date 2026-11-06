import Mathlib

theorem algebra_240460 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y + 1 / x + 1 / y + 4 = 2 * (Real.sqrt (2 * x + 1) + Real.sqrt (2 * y + 1)) ↔
    (x = 1 + Real.sqrt 2 ∧ y = 1 + Real.sqrt 2) := by
  constructor
  · -- Assume the equation holds, prove (x,y) = (1 + sqrt(2), 1 + sqrt(2))
    intro h_eq
    have h3 : x + 1 / x + 2 ≥ 2 * Real.sqrt (2 * x + 1) := by
      have h4 : x + 1 / x + 2 - 2 * Real.sqrt (2 * x + 1) ≥ 0 := by
        have h5 : 0 < x := hx
        have h6 : x + 1 / x + 2 - 2 * Real.sqrt (2 * x + 1) = (x ^ 2 + 1 + 2 * x - 2 * x * Real.sqrt (2 * x + 1)) / x := by
          field_simp
          <;> ring
        rw [h6]
        have h8 : x ^ 2 + 1 + 2 * x - 2 * x * Real.sqrt (2 * x + 1) ≥ 0 := by
          have h9 : Real.sqrt (2 * x + 1) ≥ 0 := Real.sqrt_nonneg (2 * x + 1)
          nlinarith [sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x - (1 + Real.sqrt 2)), 
            sq_nonneg (x + 1 - Real.sqrt (2 * x + 1) * Real.sqrt 2), 
            Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x + 1 by nlinarith), 
            sq_nonneg (x - 1), sq_nonneg (x * (x - 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h11 : (x ^ 2 + 1 + 2 * x - 2 * x * Real.sqrt (2 * x + 1)) / x ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        linarith
      linarith
    have h3' : y + 1 / y + 2 ≥ 2 * Real.sqrt (2 * y + 1) := by
      have h4 : y + 1 / y + 2 - 2 * Real.sqrt (2 * y + 1) ≥ 0 := by
        have h5 : 0 < y := hy
        have h6 : y + 1 / y + 2 - 2 * Real.sqrt (2 * y + 1) = (y ^ 2 + 1 + 2 * y - 2 * y * Real.sqrt (2 * y + 1)) / y := by
          field_simp
          <;> ring
        rw [h6]
        have h8 : y ^ 2 + 1 + 2 * y - 2 * y * Real.sqrt (2 * y + 1) ≥ 0 := by
          have h9 : Real.sqrt (2 * y + 1) ≥ 0 := Real.sqrt_nonneg (2 * y + 1)
          nlinarith [sq_nonneg (y ^ 2 - 2 * y - 1), sq_nonneg (y - (1 + Real.sqrt 2)), 
            sq_nonneg (y + 1 - Real.sqrt (2 * y + 1) * Real.sqrt 2), 
            Real.sqrt_nonneg (2 * y + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * y + 1 by nlinarith), 
            sq_nonneg (y - 1), sq_nonneg (y * (y - 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h11 : (y ^ 2 + 1 + 2 * y - 2 * y * Real.sqrt (2 * y + 1)) / y ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        linarith
      linarith
    have h7 : x + 1 / x + 2 = 2 * Real.sqrt (2 * x + 1) := by
      nlinarith [h3, h3', h_eq]
    have h8 : y + 1 / y + 2 = 2 * Real.sqrt (2 * y + 1) := by
      nlinarith [h3, h3', h_eq]
    have h9 : x = 1 + Real.sqrt 2 := by
      have h7' : x + 1 / x + 2 = 2 * Real.sqrt (2 * x + 1) := h7
      have h10 : 0 < x := hx
      have h11 : (x ^ 2 - 2 * x - 1) ^ 2 = 0 := by
        have h12 : Real.sqrt (2 * x + 1) ≥ 0 := Real.sqrt_nonneg (2 * x + 1)
        have h13 : x > 0 := by linarith
        have h14 : (x ^ 2 + 1 + 2 * x) = 2 * x * Real.sqrt (2 * x + 1) := by
          have h15 : x > 0 := by linarith
          field_simp at h7' ⊢
          nlinarith [Real.sqrt_nonneg (2 * x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x + 1 by nlinarith)]
        have h15 : (x ^ 2 + 1 + 2 * x) ^ 2 = 4 * x ^ 2 * (2 * x + 1) := by
          calc
            (x ^ 2 + 1 + 2 * x) ^ 2 = (2 * x * Real.sqrt (2 * x + 1)) ^ 2 := by 
              rw [h14]
            _ = 4 * x ^ 2 * (Real.sqrt (2 * x + 1) ^ 2) := by 
              ring_nf
            _ = 4 * x ^ 2 * (2 * x + 1) := by
              rw [Real.sq_sqrt (by nlinarith)]
        nlinarith [sq_nonneg (x ^ 2 - 2 * x - 1)]
      have h10 : x ^ 2 - 2 * x - 1 = 0 := by
        have h11' : (x ^ 2 - 2 * x - 1) ^ 2 = 0 := h11
        have : x ^ 2 - 2 * x - 1 = 0 := by
          apply pow_eq_zero 
          exact h11'
        assumption
      have h14 : (x - (1 + Real.sqrt 2)) * (x - (1 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0)]
      cases' (mul_eq_zero.1 h14) with h15 h16
      · -- x = 1 + Real.sqrt 2
        linarith
      · -- x = 1 - Real.sqrt 2 < 0
        have h17 : x < 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0)]
        linarith
    have h10 : y = 1 + Real.sqrt 2 := by
      have h8' : y + 1 / y + 2 = 2 * Real.sqrt (2 * y + 1) := h8
      have h11 : 0 < y := hy
      have h12 : (y ^ 2 - 2 * y - 1) ^ 2 = 0 := by
        have h13 : Real.sqrt (2 * y + 1) ≥ 0 := Real.sqrt_nonneg (2 * y + 1)
        have h14 : y > 0 := by linarith
        have h15 : (y ^ 2 + 1 + 2 * y) = 2 * y * Real.sqrt (2 * y + 1) := by
          have h16 : y > 0 := by linarith
          field_simp at h8' ⊢
          nlinarith [Real.sqrt_nonneg (2 * y + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * y + 1 by nlinarith)]
        have h16 : (y ^ 2 + 1 + 2 * y) ^ 2 = 4 * y ^ 2 * (2 * y + 1) := by
          calc
            (y ^ 2 + 1 + 2 * y) ^ 2 = (2 * y * Real.sqrt (2 * y + 1)) ^ 2 := by 
              rw [h15]
            _ = 4 * y ^ 2 * (Real.sqrt (2 * y + 1) ^ 2) := by 
              ring_nf
            _ = 4 * y ^ 2 * (2 * y + 1) := by
              rw [Real.sq_sqrt (by nlinarith)]
        nlinarith [sq_nonneg (y ^ 2 - 2 * y - 1)]
      have h13 : y ^ 2 - 2 * y - 1 = 0 := by
        have h14 : (y ^ 2 - 2 * y - 1) ^ 2 = 0 := h12
        have : y ^ 2 - 2 * y - 1 = 0 := by
          apply pow_eq_zero 
          exact h14
        assumption
      have h14 : (y - (1 + Real.sqrt 2)) * (y - (1 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0)]
      cases' (mul_eq_zero.1 h14) with h15 h16
      · -- y = 1 + Real.sqrt 2
        linarith
      · -- y = 1 - Real.sqrt 2 < 0
        have h17 : y < 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0)]
        linarith
    constructor
    · exact h9
    · exact h10
  · -- Assume (x,y) = (1 + sqrt(2), 1 + sqrt(2)), prove the equation
    rintro ⟨rfl, rfl⟩
    have h1 : Real.sqrt (2 * (1 + Real.sqrt 2) + 1) = 1 + Real.sqrt 2 := by
      have h2 : (1 + Real.sqrt 2) ^ 2 = 2 * (1 + Real.sqrt 2) + 1 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0)]
      have h3 : Real.sqrt (2 * (1 + Real.sqrt 2) + 1) = 1 + Real.sqrt 2 := by
        rw [← h2]
        field_simp [Real.sqrt_sq (show 0 ≤ 1 + Real.sqrt 2 by positivity)]
      exact h3
    field_simp [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]