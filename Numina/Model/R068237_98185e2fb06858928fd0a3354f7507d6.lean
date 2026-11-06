import Mathlib

theorem number_theory_68248 {a b c d : ℕ} (ha : a = 1) (hb : b = 2) (hc : c = 3) (hd : d = 5) :
    Nat.Prime (a * b + c * d) ∧ Nat.Prime (a * c + b * d) ∧ Nat.Prime (a * d + b * c) ∧ Nat.Prime (b * c + a * d) := by
  rw [ha, hb, hc, hd]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num