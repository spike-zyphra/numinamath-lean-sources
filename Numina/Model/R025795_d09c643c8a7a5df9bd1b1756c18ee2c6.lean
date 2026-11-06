import Mathlib

theorem inequalities_254595 (a b c x y z : ℝ) (ha : a > b) (hb : b > c)
    (hx : x > y) (hy : y > z) (hM : M = a * x + b * y + c * z)
    (hN : N = a * z + b * y + c * x) (hP : P = a * y + b * z + c * x)
    (hQ : Q = a * z + b * x + c * y) :
    M > P ∧ P > N ∧ M > Q ∧ Q > N := by
  constructor
  · -- Show that M > P
    rw [hM, hP]
    have h1 : a * x + b * y + c * z > a * y + b * z + c * x := by
      nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hy), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hy)]
    linarith
  constructor
  · -- Show that P > N
    rw [hP, hN]
    have h2 : a * y + b * z + c * x > a * z + b * y + c * x := by
      nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hy), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hy)]
    linarith
  constructor
  · -- Show that M > Q
    rw [hM, hQ]
    have h3 : a * x + b * y + c * z > a * z + b * x + c * y := by
      nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hy), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hy)]
    linarith
  · -- Show that Q > N
    rw [hQ, hN]
    have h4 : a * z + b * x + c * y > a * z + b * y + c * x := by
      nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hy), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hx), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hy)]
    linarith