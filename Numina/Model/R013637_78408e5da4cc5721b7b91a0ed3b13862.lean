import Mathlib

theorem algebra_63 {k : ℝ} (hk : k ≠ 0) (A B : ℝ × ℝ)
(hA : A.1 + 2 = k / A.1) (hB : B.1 + 2 = k / B.1)
(hAB : |A.1 - B.1| = 2 * √2) :
k = 1 := by
  have h1 : A.1 ≠ 0 := by
    by_contra h
    have hA' : A.1 + 2 = k / A.1 := hA
    rw [h] at hA'
    field_simp at hA'
  have h2 : B.1 ≠ 0 := by
    by_contra h
    have hB' : B.1 + 2 = k / B.1 := hB
    rw [h] at hB'
    field_simp at hB'
  have eq1 : A.1 ^ 2 + 2 * A.1 - k = 0 := by
    have hA' : A.1 + 2 = k / A.1 := hA
    field_simp [h1] at hA' ⊢
    linarith
  have eq2 : B.1 ^ 2 + 2 * B.1 - k = 0 := by
    have hB' : B.1 + 2 = k / B.1 := hB
    field_simp [h2] at hB' ⊢
    linarith
  have h3 : (A.1 - B.1) * (A.1 + B.1 + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Prove that $A.1 = B.1$ leads to a contradiction
    have h4' : A.1 - B.1 = 0 := h4
    have h4'' : A.1 = B.1 := by linarith
    have h5 : |A.1 - B.1| = 0 := by
      rw [show A.1 - B.1 = (0 : ℝ) by linarith [h4'']]
      all_goals norm_num
    rw [h5] at hAB
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Now we have $A.1 + b.1 = -2$
    have h6 : A.1 + B.1 = -2 := by linarith
    have h7 : (A.1 - B.1) ^ 2 = (2 * √2) ^ 2 := by
      calc
        (A.1 - B.1) ^ 2 = (|A.1 - B.1|) ^ 2 := by rw [sq_abs]
        _ = (2 * √2) ^ 2 := by rw [hAB]
    have h8 : (2 * √2) ^ 2 = (8 : ℝ) := by
      calc
        (2 * √2) ^ 2 = (2 : ℝ) ^ 2 * (√2) ^ 2 := by ring
        _ = 4 * (2 : ℝ) := by norm_num [Real.sq_sqrt]
        _ = (8 : ℝ) := by norm_num
    have h9 : (A.1 - B.1) ^ 2 = (8 : ℝ) := by
      rw [h7, h8]
    -- find k by expanding
    nlinarith [sq_nonneg (A.1 + B.1), sq_nonneg (A.1 - B.1), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h8, h9, h6, eq1, eq2]