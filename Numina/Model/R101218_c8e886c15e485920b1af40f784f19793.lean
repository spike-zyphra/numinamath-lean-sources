import Mathlib

theorem number_theory_154239 (f : ℕ → ℕ) (hf : f 0 = 98)
    (h : ∀ n, f (n + 1) = (Nat.digits 10 (f n)).prod + 15) :
    f 60 = 23 := by
  norm_num [hf, h]