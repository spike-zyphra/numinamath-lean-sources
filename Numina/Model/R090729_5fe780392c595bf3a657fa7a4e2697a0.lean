import Mathlib

theorem other_255321 (a b c d e : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e)
    (h5 : b ≠ c) (h6 : b ≠ d) (h7 : b ≠ e) (h8 : c ≠ d) (h9 : c ≠ e) (h10 : d ≠ e)
    (h11 : a * 20 + b * 30 = 12 * 20 + 9 * 30) (h12 : a * 30 + b * 20 = 10 * 20 + 2 * 30)
    (h13 : b * 20 + c * 30 = 19 * 20 + 1 * 30) :
    a = 12 ∧ b = 9 ∧ c = 10 ∧ d = 2 ∧ e = 19 := by 
  have h14 : a = 12 := by
    omega
  have h15 : b = 9 := by
    omega
  have h16 : c = 10 := by
    omega
  have h17 : d = 2 := by
    omega
  have h18 : e = 19 := by
    omega
  tauto