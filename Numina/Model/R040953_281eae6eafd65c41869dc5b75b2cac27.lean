import Mathlib

open Real
open scoped BigOperators

theorem algebra_319517 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (h''' : 1 / a + 1 / b - 1 / c = 1 / (a + b - c)) :
  a = c ∨ b = c := by
  have h1 : a + b - c > 0 := by linarith
  have ha1 : a ≠ 0 := by linarith
  have hb1 : b ≠ 0 := by linarith
  have hc1 : c ≠ 0 := by linarith
  have ha2 : a + b - c ≠ 0 := by linarith
  have h4 : (a + b - c) * (c * (a + b) - a * b - c^2) = 0 := by
    field_simp [ha1, hb1, hc1, ha2] at h''' ⊢
    ring_nf at h''' ⊢
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_pos_of_pos (show 0 < a + b - c by linarith)]
  cases' (mul_eq_zero.mp h4) with h7 h8
  · -- h7 : a + b - c = 0
    exfalso
    nlinarith
  · -- h8 : c * (a + b) - a * b - c^2 = 0
    have h10 : (c - b) * (a - c) = 0 := by
      nlinarith
      <;> nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- c - b = 0
      right
      linarith
    · -- a - c = 0
      left
      nlinarith