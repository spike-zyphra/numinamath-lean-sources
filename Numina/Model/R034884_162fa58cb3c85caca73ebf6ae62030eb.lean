import Mathlib

theorem number_theory_213025 {A : ℕ} (h1 : A % 1981 = 35) (h2 : A % 1982 = 35) :
    A % 14 = 7 := by 
  omega