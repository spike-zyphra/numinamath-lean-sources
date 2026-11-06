import Mathlib

theorem algebra_295013 (x1 x2 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hxy : x1 ≠ x2)
    (a : ℝ) (ha : 0 < a ∧ a < 1) (y1 y2 : ℝ)
    (hy1 : y1 = x1 / (1 + a) + a * x2 / (1 + a)) (hy2 : y2 = x2 / (1 + a) + a * x1 / (1 + a)) :
    x1 * x2 < y1 * y2 := by 
  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have h1 : 0 < 1 + a := by linarith
  have eq1 : y1 * y2 = (x1 + a * x2) * (x2 + a * x1) / ((1 + a) ^ 2) := by
    rw [hy1, hy2]
    field_simp [(show 0 < 1 + a by linarith)]
    <;> ring
  have eq2 : y1 * y2 - x1 * x2 = (a * (x1 - x2) ^ 2) / ((1 + a) ^ 2) := by
    rw [eq1]
    field_simp [(show 0 < 1 + a by linarith)]
    ring_nf
  have h2 : a * (x1 - x2) ^ 2 > 0 := by
    have hne : (x1 - x2) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero 
      intro h 
      apply hxy 
      linarith
    nlinarith
  have h3 : a * (x1 - x2) ^ 2 / ((1 + a) ^ 2) > 0 := by 
    apply div_pos
    linarith
    nlinarith
  have eq3 : y1 * y2 - x1 * x2 > 0 := by 
    linarith [eq2, h3]
  linarith [eq3]