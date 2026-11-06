import Mathlib

theorem number_theory_15751 (a b : ℤ) (ha : a % 70 = 64) (hb : b % 105 = 99) :
    (a + b) % 35 = 23 := by
  have h1 : a % 35 = 29 := by
    have h2 : a % 70 = 64 := ha
    omega
  have h3 : b % 35 = 29 := by
    have h4 : b % 105 = 99 := hb
    omega
  have h5 : (a + b) % 35 = 23 := by
    omega
  exact h5