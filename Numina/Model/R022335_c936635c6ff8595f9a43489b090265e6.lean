import Mathlib

theorem inequalities_602443 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 ≤ 1 / (1 + a)^2 + 1 / (1 + b)^2 + 1 / (1 + c)^2 + 1 / (1 + d)^2 := by
  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 ≥ 1 / (1 + x * y) := by
    intro x y hx hy
    have h3 : 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 - 1 / (1 + x * y) ≥ 0 := by
      have pos1 : 0 < (1 + x) ^ 2 * (1 + y) ^ 2 * (1 + x * y) := by
        positivity
      have h4 : (1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 - 1 / (1 + x * y)) =
          ((1 + y) ^ 2 * (1 + x * y) + (1 + x) ^ 2 * (1 + x * y) - (1 + x) ^ 2 * (1 + y) ^ 2) / ((1 + x) ^ 2 * (1 + y) ^ 2 * (1 + x * y)) := by
        field_simp
        <;> ring
      rw [h4]
      apply div_nonneg
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x * (y)), sq_nonneg ((1 + x) * (1 + y) - 2), mul_nonneg (show (0 : ℝ) ≤ x by linarith [hx]) (show (0 : ℝ) ≤ y by linarith [hy]), sq_nonneg (x * y), sq_nonneg ((1 + x) * (1 + y)), sq_nonneg ((1 + x * y) ) ]
      positivity
    linarith
  have h2 : 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 ≥ 1 / (1 + a * b) := by
    apply h1 a b ha hb
  have h3 : 1 / (1 + c) ^ 2 + 1 / (1 + d) ^ 2 ≥ 1 / (1 + c * d) := by
    apply h1 c d hc hd
  have h4 : a * b > 0 := mul_pos ha hb
  have h5 : c * d > 0 := mul_pos hc hd
  have h6 : (a * b) * (c * d) = 1 := by
    nlinarith
  have h7 : 1 / (1 + a * b) + 1 / (1 + c * d) ≥ 1 := by
    have h8 : c * d = 1 / (a * b) := by
      field_simp
      nlinarith
    rw [h8]
    have h10 : 0 < a * b := mul_pos ha hb
    have h11 : (1 / (1 + a * b) + 1 / (1 + 1 / (a * b)) ) = 1 := by
      field_simp
      all_goals nlinarith
    nlinarith [h11]
  linarith [h2, h3, h7]