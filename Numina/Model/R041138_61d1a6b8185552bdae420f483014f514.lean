import Mathlib

theorem algebra_27982 (x y z a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a < b ∧ b < c) (hx : x = -2272) (hy : y = 10^3 + 10^2 * c + 10 * b + a)
    (hz : z = 1) (h : a * x + b * y + c * z = 1) :
    y = 1987 := by
  rw [hx, hy, hz] at h
  ring_nf at h
  rcases hord with ⟨h1, h2⟩
  have h3 : a ≤ 9 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc]
  have h4 : b ≤ 22 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc]
  have h5 : c ≤ 23 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc]
  interval_cases a <;> interval_cases b <;> omega