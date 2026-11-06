import Mathlib

theorem algebra_86645 (x y a b : ℝ) (hx : 0 < x) (hy : 0 < y)
    (ha : a = 1 + x / y) (hb : b = 1 + y / x) (h : a ^ 2 + b ^ 2 = 15) :
    a ^ 3 + b ^ 3 = 50 := by
  have h1 : a * b = 2 + x / y + y / x := by
    rw [ha, hb]
    field_simp [show 0 < x * y by positivity]
    <;> ring
  have h2 : a + b = 2 + x / y + y / x := by
    rw [ha, hb]
    ring_nf
  have h3 : a + b = a * b := by
    linarith [h1, h2]
  have h4 : (a + b) ^ 2 = (a * b) ^ 2 := by
    have h5 : a + b = a * b := by
      linarith [h3]
    rw [h5]
  have h5 : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by
    ring
  rw [h5] at h4
  rw [h] at h4
  have h6 : (a * b) ^ 2 - 2 * (a * b) - 15 = 0 := by
    nlinarith
  have h9 : a * b = 5 := by
    have h8 : 0 < a * b := by
      have ha1 : 0 < a := by
        rw [ha]
        have h1 : x / y > 0 := by positivity
        linarith
      have hb1 : 0 < b := by
        rw [hb]
        have h1 : y / x > 0 := by positivity
        linarith
      positivity
    have h8 : (a * b - 5) * (a * b + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h8) with h8 h8
    · linarith
    · nlinarith
  have h8 : a + b = 5 := by
    nlinarith [h3, h9]
  calc
    a ^ 3 + b ^ 3 = (a + b) * ((a) ^ 2 + (b) ^ 2 - (a * b)) := by
      ring
    _ = (5) * (15 - 5) := by
      rw [h8]
      have h10 : a ^ 2 + b ^ 2 = 15 := by
        linarith
      have h11 : a * b = 5 := by
        linarith
      rw [h10, h11]
    _ = 50 := by
      norm_num