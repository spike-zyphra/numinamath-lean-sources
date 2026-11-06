import Mathlib

theorem inequalities_47742 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 3) :
    1 / (x ^ 2 + y + z) + 1 / (x + y ^ 2 + z) + 1 / (x + y + z ^ 2) ≤ 1 := by
  have h1 : 0 < x ^ 2 + y + z := by
    nlinarith
  have h2 : 0 < x + y ^ 2 + z := by
    nlinarith
  have h3 : 0 < x + y + z ^ 2 := by
    nlinarith
  have hx2 : x ^ 2 + y + z = x^2 - x + 3 := by
    nlinarith
  have hy2 : x + y ^ 2 + z = y^2 - y + 3 := by
    nlinarith
  have hz2 : x + y + z ^ 2 = z^2 - z + 3 := by
    nlinarith
  have h7 : 1 / (x ^ 2 - x + 3) ≤ 1 / 3 - (1 / 9) * (x - 1) := by 
    have hx3 : 0 < x^2 - x + 3 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have h9 : (x - 1) ^ 2 * (x - 3) ≤ 0 := by
      have h9 : x ≤ 3 := by nlinarith
      have h10 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
      nlinarith
    have h12 : (1 / 3 - (1 / 9) * (x - 1)) * (x ^ 2 - x + 3) ≥ 1 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x - 2)), h9]
    have h6 : 1 / (x ^ 2 - x + 3) ≤ (1 / 3 - (1 / 9) * (x - 1)) := by
      have hx32 : 0 < x^2 - x + 3 := by nlinarith [sq_nonneg (x - 1 / 2)]
      apply (div_le_iff₀ (by nlinarith)).mpr
      nlinarith
    linarith
  have h8 : 1 / (y ^ 2 - y + 3) ≤ 1 / 3 - (1 / 9) * (y - 1) := by 
    have hy3 : 0 < y^2 - y + 3 := by nlinarith [sq_nonneg (y - 1 / 2)]
    have h9 : (y - 1) ^ 2 * (y - 3) ≤ 0 := by
      have h9 : y ≤ 3 := by nlinarith
      have h10 : (y - 1) ^ 2 ≥ 0 := sq_nonneg (y - 1)
      nlinarith
    have h13 : (1 / 3 - (1 / 9) * (y - 1)) * (y ^ 2 - y + 3) ≥ 1 := by 
      nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 2), sq_nonneg (y * (y - 1)), sq_nonneg ((y - 1) * (y - 2)), h9]
    have h6 : 1 / (y ^ 2 - y + 3) ≤ (1 / 3 - (1 / 9) * (y - 1)) := by
      have hy32 : 0 < y^2 - y + 3 := by nlinarith [sq_nonneg (y - 1 / 2)]
      apply (div_le_iff₀ (by nlinarith)).mpr
      nlinarith
    linarith
  have h9 : 1 / (z ^ 2 - z + 3) ≤ 1 / 3 - (1 / 9) * (z - 1) := by 
    have hz3 : 0 < z^2 - z + 3 := by nlinarith [sq_nonneg (z - 1 / 2)]
    have h9 : (z - 1) ^ 2 * (z - 3) ≤ 0 := by
      have h9 : z ≤ 3 := by nlinarith
      have h10 : (z - 1) ^ 2 ≥ 0 := sq_nonneg (z - 1)
      nlinarith
    have h13 : (1 / 3 - (1 / 9) * (z - 1)) * (z ^ 2 - z + 3) ≥ 1 := by 
      nlinarith [sq_nonneg (z - 1), sq_nonneg (z - 2), sq_nonneg (z * (z - 1)), sq_nonneg ((z - 1) * (z - 2)), h9]
    have h6 : 1 / (z ^ 2 - z + 3) ≤ (1 / 3 - (1 / 9) * (z - 1)) := by
      have hz32 : 0 < z^2 - z + 3 := by nlinarith [sq_nonneg (z - 1 / 2)]
      apply (div_le_iff₀ (by nlinarith)).mpr
      nlinarith
    linarith
  have hx6 : 1 / (x ^ 2 + y + z) + 1 / (x + y ^ 2 + z) + 1 / (x + y + z ^ 2) ≤ ((1 / 3) - (1 / 9) * (x - 1)) + ((1 / 3) - (1 / 9) * (y - 1)) + ((1 / 3) - (1 / 9) * (z - 1)) := by
    have h10 : 1 / (x ^ 2 + y + z) ≤ (1 / 3) - (1 / 9) * (x - 1) := by 
      rw [show x ^ 2 + y + z = x^2 - x + 3 by nlinarith]
      exact h7
    have h11 : 1 / (x + y ^ 2 + z) ≤ (1 / 3) - (1 / 9) * (y - 1) := by 
      rw [show x + y ^ 2 + z = y^2 - y + 3 by nlinarith]
      exact h8
    have h12 : 1 / (x + y + z ^ 2) ≤ (1 / 3) - (1 / 9) * (z - 1) := by 
      rw [show x + y + z ^ 2 = z^2 - z + 3 by nlinarith]
      exact h9
    linarith [h10, h11, h12]
  have hx7 : ((1 / 3) - (1 / 9) * (x - 1)) + ((1 / 3) - (1 / 9) * (y - 1)) + ((1 / 3) - (1 / 9) * (z - 1)) = 1 := by
    field_simp
    nlinarith [hsum]
  linarith [hx6, hx7]