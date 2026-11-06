import Mathlib

theorem inequalities_263946 (a b c d : ℝ) (ha : a > b) (hb : a > c) (hc : a > d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : a * b + c * d > b * c + a * d)
    (h2 : b * c + a * d > a * c + b * d) :
    min (min a b) (min c d) = c := by
  have h3 : (b - d) * (a - c) > 0 := by
    linarith
  have h4 : b - d > 0 := by
    have h5 : a - c > 0 := by linarith
    nlinarith
  have h6 : (c - d) * (b - a) > 0 := by
    linarith
  have h7 : c - d < 0 := by
    have h8 : b - a < 0 := by linarith
    nlinarith
  have h8 : b > d := by linarith
  have h9 : c < d := by linarith
  have h10 : a > b := by linarith
  have h11 : min (min a b) (min c d) = c := by
    have h12 : min a b = b := by
      apply min_eq_right
      linarith
    have h13 : min c d = c := by
      apply min_eq_left
      linarith
    have h14 : b > c := by
      linarith
    rw [h12, h13]
    apply min_eq_right
    linarith
  exact h11