import Mathlib

theorem algebra_1001 {x y a b c : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hxy : x / y = a / b) (hc : x + y = c) (hord : a < b) :
    max x y = (b * c / (a + b)) := by

  have h1 : x * b = a * y := by
    have h2 : 0 < y := hy
    have h3 : 0 < b := hb
    field_simp [h2, h3] at hxy ⊢
    linarith

  have h2 : y = c - x := by
    linarith

  rw [h2] at h1

  have h3 : x * (a + b) = a * c := by
    linarith

  have h4 : x = a * c / (a + b) := by
    field_simp [(show 0 < a + b by nlinarith)]
    <;> nlinarith

  have h5 : y = b * c / (a + b) := by
    have h6 : y = c - x := by
      linarith
    rw [h6, h4]
    field_simp [(show 0 < a + b by nlinarith)]
    <;> nlinarith

  have h6 : x < y := by
    have h7 : x = a * c / (a + b) := h4
    have h8 : y = b * c / (a + b) := h5
    rw [h7, h8]
    apply (div_lt_div_right (by positivity)).mpr
    nlinarith [show 0 < c by nlinarith, hord]

  have h7 : max x y = y := by
    apply max_eq_right
    linarith [h6]

  rw [h7, h5]