import Mathlib

theorem algebra_18688 {a b c d : ℤ} (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : a + b = 10) (h2 : a + c = 18)
    (h3 : a + d = 19) (h4 : b + c = 20) (h5 : b + d = 21) (h6 : c + d = 29) :
    a = 4 ∧ b = 6 ∧ c = 14 ∧ d = 15 := by
  have h7 : b = 6 := by
    have eq1 : a = 10 - b := by
      omega
    have eq2 : c = 20 - b := by
      omega
    have eq3 : a + c = 18 := by
      linarith
    rw [eq1, eq2] at eq3
    linarith
  have ha2 : a = 4 := by
    linarith [h1, h7]
  have hc2 : c = 14 := by
    linarith [h4, h7]
  have hd2 : d = 15 := by
    have eq1 : d = 21 - b := by
      omega
    rw [h7] at eq1
    omega
  exact ⟨ha2, h7, hc2, hd2⟩