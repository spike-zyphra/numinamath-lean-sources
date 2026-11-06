import Mathlib

theorem number_theory_14436 (f : ℕ → ℕ) (hf1 : f 1 = 1)
    (hfn : ∀ n, 1 ≤ n → f (n + 1) = 10 ^ (Nat.digits 10 (n + 1)).length * f n + n + 1) :
    f 44 % 45 = 9 := by 
  norm_num [hf1, hfn]