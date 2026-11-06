import Mathlib
open Real
theorem algebra_96012 (a b c d : ℕ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
  (h1 : (a + b + c:ℝ) / 3 + d = 29)
  (h2 : (a + b + d:ℝ) / 3 + c = 23)
  (h3 : (a + c + d:ℝ) / 3 + b = 21)
  (h4 : (b + c + d:ℝ) / 3 + a = 17)
: d = 21 := by
  have eq1 : (a + b + c + 3 * d : ℝ) = 87 := by
    linarith
  have eq2 : (a + b + d + 3 * c : ℝ) = 69 := by
    linarith
  have eq3 : (a + c + d + 3 * b : ℝ) = 63 := by
    linarith
  have eq4 : (b + c + d + 3 * a : ℝ) = 51 := by
    linarith
  have h5 : (a + b + c + d : ℝ) = 45 := by
    linarith [eq1, eq2, eq3, eq4]
  have hd21 : (d : ℝ) = 21 := by
    have h1' : (a + b + c + 3 * d : ℝ) = 87 := eq1
    have h5' : (a + b + c + d : ℝ) = 45 := h5
    linarith
  have h6 : d = 21 := by
    exact_mod_cast hd21
  exact h6