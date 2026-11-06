import Mathlib

theorem algebra_274916 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a * b + c * d = 38) (h2 : a * c + b * d = 34) (h3 : a * d + b * c = 43) :
    a + b + c + d = 18 := by

  have h4 : (a + b) * (c + d) = 77 := by
    nlinarith

  have h5 : (a + b) = 7 ∨ (a + b) = 11 := by
    have h6 : (a + b) * (c + d) = 77 := h4
    have h7 : (a + b) ∣ 77 := by
      use (c + d)
      linarith
    have h8 : (a + b) ∣ 77 := h7
    have h9 : (a + b) ≤ 77 := by
      exact Nat.le_of_dvd (by norm_num) h7
    interval_cases hab : (a + b) <;> omega

  rcases h5 with h5 | h5
  · -- Case where $a + b = 7$ which gives $c + d = 11$
    have h5' : c + d = 11 := by
      nlinarith [h4, h5]
    have h6 : a ≤ 7 := by
      omega
    have h7 : b ≤ 7 := by
      omega
    have h8 : c ≤ 11 := by
      omega
    have h9 : d ≤ 11 := by
      omega
    interval_cases a <;> omega

  · -- Case where $a + b = 11$ which gives $c + d = 7$
    have h5' : c + d = 7 := by
      nlinarith [h4, h5]
    have h6 : a ≤ 11 := by
      omega
    have h7 : b ≤ 11 := by
      omega
    have h8 : c ≤ 7 := by
      omega
    have h9 : d ≤ 7 := by
      omega
    interval_cases a <;> omega