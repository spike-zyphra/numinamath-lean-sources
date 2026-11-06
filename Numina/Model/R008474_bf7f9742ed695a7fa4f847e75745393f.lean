import Mathlib

theorem number_theory_13385 (s : ℕ → ℕ)
    (hs: ∀n, s n = (Nat.digits 2 n).foldr (fun a b ↦ b * 3 + a) 0) :
    s 100 = 981 := by 
  rw [hs 100]
  norm_num [Nat.digits, Nat.digitsAux]