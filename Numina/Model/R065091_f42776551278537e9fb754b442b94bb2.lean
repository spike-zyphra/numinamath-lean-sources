import Mathlib

theorem number_theory_629 : ((Finset.Icc 10 99).filter fun (x : ℕ) => (x / 10 : ℕ) % 10 > (x % 10 : ℕ)).card = 45 := by 
  native_decide