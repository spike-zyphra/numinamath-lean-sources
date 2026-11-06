import Mathlib

theorem inequalities_305268 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    (a ^ 2 + 9) / (2 * a ^ 2 + (b + c) ^ 2) +
    (b ^ 2 + 9) / (2 * b ^ 2 + (c + a) ^ 2) +
    (c ^ 2 + 9) / (2 * c ^ 2 + (a + b) ^ 2) ≤ 5 := by
  have h1 : b + c = 3 - a := by linarith
  have h2 : c + a = 3 - b := by linarith
  have h3 : a + b = 3 - c := by linarith
  have h4 : 2 * a ^ 2 + (b + c) ^ 2 = 3 * a ^ 2 - 6 * a + 9 := by
    rw [h1]
    nlinarith
  have h5 : 2 * b ^ 2 + (c + a) ^ 2 = 3 * b ^ 2 - 6 * b + 9 := by
    rw [h2]
    nlinarith
  have h6 : 2 * c ^ 2 + (a + b) ^ 2 = 3 * c ^ 2 - 6 * c + 9 := by
    rw [h3]
    nlinarith
  have h7 : (a ^ 2 + 9) / (2 * a ^ 2 + (b + c) ^ 2) =
      (a ^ 2 + 9) / (3 * a ^ 2 - 6 * a + 9) := by
    rw [h4]
  have h8 : (b ^ 2 + 9) / (2 * b ^ 2 + (c + a) ^ 2) =
      (b ^ 2 + 9) / (3 * b ^ 2 - 6 * b + 9) := by
    rw [h5]
  have h9 : (c ^ 2 + 9) / (2 * c ^ 2 + (a + b) ^ 2) =
      (c ^ 2 + 9) / (3 * c ^ 2 - 6 * c + 9) := by
    rw [h6]
  rw [h7, h8, h9]
  have h10 : (a ^ 2 + 9) / (3 * a ^ 2 - 6 * a + 9) ≤ (a + 4) / 3 := by
    apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 3)]
  have h11 : (b ^ 2 + 9) / (3 * b ^ 2 - 6 * b + 9) ≤ (b + 4) / 3 := by
    apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
    nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 3)]
  have h12 : (c ^ 2 + 9) / (3 * c ^ 2 - 6 * c + 9) ≤ (c + 4) / 3 := by
    apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 3)]
  have h13 : (a + 4) / 3 + (b + 4) / 3 + (c + 4) / 3 = 5 := by
    field_simp
    <;> nlinarith [h]
  linarith [h10, h11, h12, h13]