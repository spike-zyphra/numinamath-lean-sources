import Mathlib

theorem algebra_309900 {a b c : ℝ} (ha : a ≠ -1) (hb : b ≠ -3) (hc : c ≠ -5)
    (h : a + b + c = 1) (h1 : 1 / (a + 1) + 1 / (b + 3) + 1 / (c + 5) = 0) :
    (a + 1)^2 + (b + 3)^2 + (c + 5)^2 = 100 := by
  have h2 : a + 1 ≠ 0 := by
    intro h2
    apply ha
    linarith
  have h3 : b + 3 ≠ 0 := by
    intro h3
    apply hb
    linarith
  have h4 : c + 5 ≠ 0 := by
    intro h4
    apply hc
    linarith
  have eq1 : (b + 3) * (c + 5) + (a + 1) * (c + 5) + (a + 1) * (b + 3) = 0 := by
    field_simp [h2, h3, h4] at h1
    nlinarith
  have h5 : (a + 1) + (b + 3) + (c + 5) = 10 := by
    linarith [h]
  have h6 : (a + 1) * (b + 3) + (a + 1) * (c + 5) + (b + 3) * (c + 5) = 0 := by
    linarith [eq1]
  nlinarith [h5, h6]