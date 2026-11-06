import Mathlib

theorem algebra_120526 {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (h : a > b) (h' : a * b - a - b = 1) :
    (a, b) = (3, 2) := by
  have eq1 : a * b - a - b + 1 = 2 := by
    linarith
  have eq2 : (a - 1) * (b - 1) = 2 := by
    linarith
  have h1 : a - 1 > b - 1 := by
    nlinarith
  have h4 : b - 1 = 1 := by
    have h5 : b - 1 > 0 := by
      by_contra h6
      push_neg at h6
      have : a - 1 < 0 := by
        nlinarith
      nlinarith
    have h6 : b - 1 < 2 := by
      by_contra h7
      push_neg at h7
      have h7 : b - 1 >= 2 := by
          omega
      have : a - 1 <= 1 := by
        nlinarith
      nlinarith
    omega
  have h5 : a - 1 = 2 := by
    rw [h4] at eq2
    nlinarith
  have ha2 : a = 3 := by
    linarith
  have hb2 : b = 2 := by
    linarith
  simp [Prod.ext_iff, ha2, hb2]
  all_goals linarith