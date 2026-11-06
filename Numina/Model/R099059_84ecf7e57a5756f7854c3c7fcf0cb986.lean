import Mathlib

theorem number_theory_245730 (a b c : ℕ) (ha : a ∈ Finset.Icc 1 10)
    (hb : b ∈ Finset.Icc 1 10) (hc : c ∈ Finset.Icc 1 10)
    (h1 : a + b + c = 13) (h2 : b + c + a = 15) (h3 : c + a + b = 23) :
    a = 3 ∧ b = 5 ∧ c = 9 := by 
  omega