import Mathlib

open Real

theorem inequalities_214383 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 ≤ sqrt (a / (b + c)) + sqrt (b / (c + a)) + sqrt (c / (a + b)) := by

  have h1 : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → sqrt (x / (y + z)) ≥ 2 * x / (x + y + z):= by
    intro x y z hx hy hz
    have h1 : 0 < y + z := by positivity
    have h2 : sqrt (x / (y + z)) ≥ 2 * x / (x + y + z) := by
      have h3 : (2 * x / (x + y + z)) ^ 2 ≤ x / (y + z) := by
        have h5 : (2 * x) ^ 2 * (y + z) ≤ x * (x + y + z) ^ 2 := by
          nlinarith [sq_nonneg (x - (y + z))]
        have h6 : 0 < (y + z) * ((x + y + z) ^ 2) := by positivity
        have h7 : (2 * x / (x + y + z)) ^ 2 = (2 * x) ^ 2 / ((x + y + z) ^ 2) := by
          field_simp
        have h8 : (2 * x) ^ 2 / ((x + y + z) ^ 2) ≤ x / (y + z) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [sq_nonneg (x - (y + z))]
        linarith
      have h4_pos : sqrt ((2 * x / (x + y + z)) ^ 2) = 2 * x / (x + y + z) := by
        rw [Real.sqrt_sq (show 0 ≤ 2 * x / (x + y + z) by positivity)]
      have h5_pos : sqrt (x / (y + z)) ≥ 2 * x / (x + y + z) := by
        have h3_pos' : (2 * x / (x + y + z)) ^ 2 ≤ x / (y + z) := h3
        have h3_pos'' : sqrt ((2 * x / (x + y + z)) ^ 2) ≤ sqrt (x / (y + z)) := Real.sqrt_le_sqrt h3_pos'
        rw [h4_pos] at h3_pos''
        linarith
      linarith
    linarith

  have h2 := h1 a b c ha hb hc
  have h3 := h1 b c a hb hc ha
  have h4 := h1 c a b hc ha hb

  have h5 : sqrt (a / (b + c)) + sqrt (b / (c + a)) + sqrt (c / (a + b)) ≥ 2 * a / (a + b + c) + 2 * b / (a + b + c) + 2 * c / (a + b + c) := by
    have h5 : sqrt (a / (b + c)) ≥ 2 * a / (a + b + c) := h2
    have h6 : sqrt (b / (c + a)) ≥ 2 * b / (a + b + c) := by
      have h10 : sqrt (b / (c + a)) ≥ 2 * b / (b + c + a) := by
        simpa using h3
      have h11 : 2 * b / (b + c + a) = 2 * b / (a + b + c) := by ring
      linarith [h10, h11]
    have h7 : sqrt (c / (a + b)) ≥ 2 * c / (a + b + c) := by
      have h14 : sqrt (c / (a + b)) ≥ 2 * c / (c + a + b) := by
        simpa using h4
      have h15 : 2 * c / (c + a + b) = 2 * c / (a + b + c) := by ring
      linarith [h14, h15]
    linarith [h5, h6, h7]

  have h13 : 2 * a / (a + b + c) + 2 * b / (a + b + c) + 2 * c / (a + b + c) = 2 := by
    field_simp
    <;> nlinarith
  linarith [h5, h13]