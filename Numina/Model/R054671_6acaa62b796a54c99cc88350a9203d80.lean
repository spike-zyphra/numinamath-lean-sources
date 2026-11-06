import Mathlib

theorem number_theory_263396 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * 9 = b * 8 + 1) (h2 : b * 98 = a * 99 + 1) (h3 : c * 1999 = a * 1998 + 1) :
    a = 510 ∧ b = 312 ∧ c = 462 := by
  have eq1 : a = 510 := by
    omega
  have eq2 : b = 312 := by
    omega
  have eq3 : c = 462 := by
    omega
  exact ⟨eq1, eq2, eq3⟩