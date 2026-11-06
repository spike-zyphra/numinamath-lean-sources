import Mathlib

theorem inequalities_603638
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b > c)
    (h' : a + c > b)
    (h'' : b + c > a) :
    6 ≤ (a + b) / (b + c - a) + (b + c) / (c + a - b) + (c + a) / (a + b - c) := by
  set x := (b + c - a) / 2 with hx
  set y := (c + a - b) / 2 with hy
  set z := (a + b - c) / 2 with hz
  have xpos : 0 < x := by linarith
  have ypos : 0 < y := by linarith
  have zpos : 0 < z := by linarith
  have h₁ : a + b = x + y + 2 * z := by ring
  have h₂ : b + c = 2 * x + y + z := by ring
  have h₃ : c + a = x + 2 * y + z := by ring
  calc (a + b) / (b + c - a) + (b + c) / (c + a - b) + (c + a) / (a + b - c)
    _ = (x + y + 2 * z) / (2 * x) + (2 * x + y + z) / (2 * y) + (x + 2 * y + z) / (2 * z) := by congr <;> linarith
    _ = 3 / 2 + (y / x + z / y + x / z) / 2 + (z / x + x / y + y / z) := by field_simp; ring
    _ ≥ 3 / 2 + 3 / 2 + 3 := ?_
    _ = 6 := by ring
  have H {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 ≤ y / x + z / y + x / z := by
    have h := Real.geom_mean_le_arith_mean Finset.univ ![1, 1, 1] ![y / x, z / y, x / z] ?_ ?_ ?_
    rotate_left
    . intro i
      fin_cases i <;> simp
    . norm_num [Finset.sum]
    . intro i
      fin_cases i <;> (simp; positivity)
    simp [Finset.sum, Finset.prod] at h
    simp [show y / x * (z / y * (x / z)) = 1 by field_simp; ring] at h
    linarith only [h]
  gcongr
  . exact H xpos ypos zpos
  . linarith only [H xpos zpos ypos]
