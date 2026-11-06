import Mathlib

theorem algebra_246913 (a b c d : ℤ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hsum : a + b + c = 6 ∧ a + b + d = 7 ∧ a + c + d = 8 ∧ b + c + d = 9) :
    a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 4 := by
  rcases hsum with ⟨h1, h2, h3, h4⟩
  have htotal : a + b + c + d = 10 := by
    linarith
  have ha_eq : a = 1 := by
    linarith [htotal, h4]
  have hb_eq : b = 2 := by
    linarith [htotal, h3]
  have hc_eq : c = 3 := by
    linarith [htotal, h2]
  have hd_eq : d = 4 := by
    linarith [htotal, h1]
  exact ⟨ha_eq, hb_eq, hc_eq, hd_eq⟩