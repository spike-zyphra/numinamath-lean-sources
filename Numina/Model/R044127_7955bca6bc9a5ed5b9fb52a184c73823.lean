import Mathlib

theorem number_theory_7208 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b + a * d + b * c + d * c = 40) :
    a + b + c + d = 13 ∨ a + b + c + d = 14 ∨ a + b + c + d = 22 := by
  have h1 : (a + c) * (b + d) = 40 := by
    linarith
  have h3 : (a + c) > 1 := by
    nlinarith
  have h4 : (b + d) > 1 := by
    nlinarith
  have h5 : (a + c) ≤ 20 := by
    by_contra h5
    push_neg at h5
    have h6 : (b + d) ≤ 1 := by
      nlinarith
    nlinarith
  interval_cases h6 : (a + c) <;> omega