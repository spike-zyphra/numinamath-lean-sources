import Mathlib

theorem inequalities_125390 (x y z a b c r : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) :
    (x + y + a + b) / (x + y + a + b + c + r) + (y + z + b + c) / (y + z + a + b + c + r) >
    (x + z + a + c) / (x + z + a + b + c + r) := by
  have hx1 : 0 < x + y + a + b + c + r := by
    linarith
  have hy1 : 0 < y + z + a + b + c + r := by
    linarith
  have hz1 : 0 < x + z + a + b + c + r := by
    linarith
  have h3 : (x + y + a + b) * (y + z + a + b + c + r) * (x + z + a + b + c + r) + (y + z + b + c) * (x + y + a + b + c + r) * (x + z + a + b + c + r) - (x + z + a + c) * (x + y + a + b + c + r) * (y + z + a + b + c + r) > 0 := by
    nlinarith [sq_nonneg (x + y + a + b - (y + z + b + c)), sq_nonneg (x + y + a + b - (x + z + a + c)), sq_nonneg (y + z + b + c - (x + z + a + c)),
        mul_pos hx hy, mul_pos hx hz, mul_pos hx ha, mul_pos hx hb, mul_pos hx hc, mul_pos hx hr,
        mul_pos hy hz, mul_pos hy ha, mul_pos hy hb, mul_pos hy hc, mul_pos hy hr,
        mul_pos hz ha, mul_pos hz hb, mul_pos hz hc, mul_pos hz hr,
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hr,
        mul_pos hb hc, mul_pos hb hr,
        mul_pos hc hr]
  have hx2 : 0 < (x + y + a + b + c + r) * (y + z + a + b + c + r) * (x + z + a + b + c + r) := by
    positivity
  have h4 : (x + y + a + b) / (x + y + a + b + c + r) + (y + z + b + c) / (y + z + a + b + c + r) - (x + z + a + c) / (x + z + a + b + c + r) > 0 := by
    have hx1 : 0 < x + y + a + b + c + r := by linarith
    have hy1 : 0 < y + z + a + b + c + r := by linarith
    have hz1 : 0 < x + z + a + b + c + r := by linarith 
    have hx2 : 0 < (x + y + a + b + c + r) * (y + z + a + b + c + r) * (x + z + a + b + c + r) := by positivity
    have eq1 : (x + y + a + b) / (x + y + a + b + c + r) + (y + z + b + c) / (y + z + a + b + c + r) - (x + z + a + c) / (x + z + a + b + c + r) =
        ((x + y + a + b) * (y + z + a + b + c + r) * (x + z + a + b + c + r) + (y + z + b + c) * (x + y + a + b + c + r) * (x + z + a + b + c + r) - (x + z + a + c) * (x + y + a + b + c + r) * (y + z + a + b + c + r)) / ((x + y + a + b + c + r) * (y + z + a + b + c + r) * (x + z + a + b + c + r)) := by
      field_simp
      <;> ring
    rw [eq1] at *
    apply div_pos
    · linarith [h3]
    · positivity
  linarith