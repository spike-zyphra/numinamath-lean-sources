import Mathlib

theorem algebra_120989 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    2 = Real.sqrt ((a + b * c) * (b + c * a) / (c + a * b)) +
        Real.sqrt ((b + c * a) * (c + a * b) / (a + b * c)) +
        Real.sqrt ((c + a * b) * (a + b * c) / (b + c * a)) := by
  have h1 : c + a * b = (1 - a) * (1 - b) := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h2 : a + b * c = (1 - b) * (1 - c) := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h3 : b + c * a = (1 - a) * (1 - c) := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h4 : (a + b * c) * (b + c * a) / (c + a * b) = (1 - c)^2 := by
    rw [h2, h3, h1]
    field_simp [show 1 - a ≠ 0 by nlinarith, show 1 - b ≠ 0 by nlinarith, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    <;> ring
    <;> nlinarith
  have h5 : Real.sqrt ((a + b * c) * (b + c * a) / (c + a * b)) = 1 - c := by
    rw [h4]
    have h6 : 0 ≤ (1 - c : ℝ) := by nlinarith
    have h7 : Real.sqrt ((1 - c : ℝ)^2) = (1 - c : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h6]
      all_goals nlinarith
    exact h7
  have h8 : (b + c * a) * (c + a * b) / (a + b * c) = (1 - a)^2 := by
    rw [h3, h1, h2]
    field_simp [show 1 - b ≠ 0 by nlinarith, show 1 - c ≠ 0 by nlinarith, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    <;> ring
    <;> nlinarith
  have h9 : Real.sqrt ((b + c * a) * (c + a * b) / (a + b * c)) = 1 - a := by
    rw [h8]
    have h10 : 0 ≤ (1 - a : ℝ) := by nlinarith
    have h11 : Real.sqrt ((1 - a : ℝ)^2) = (1 - a : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h10]
      all_goals nlinarith
    exact h11
  have h10 : (c + a * b) * (a + b * c) / (b + c * a) = (1 - b)^2 := by
    rw [h1, h2, h3]
    field_simp [show 1 - a ≠ 0 by nlinarith, show 1 - c ≠ 0 by nlinarith, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    <;> ring
    <;> nlinarith
  have h11 : Real.sqrt ((c + a * b) * (a + b * c) / (b + c * a)) = 1 - b := by
    rw [h10]
    have h12 : 0 ≤ (1 - b : ℝ) := by nlinarith
    have h13 : Real.sqrt ((1 - b : ℝ)^2) = (1 - b : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h12]
      all_goals nlinarith
    exact h13
  rw [h5, h9, h11]
  have h14 : (1 - c : ℝ) + (1 - a : ℝ) + (1 - b : ℝ) = (2 : ℝ) := by
    nlinarith [h]
  linarith [h14]