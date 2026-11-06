import Mathlib

open Real

theorem number_theory_133649 {p : ℕ} (hp : Nat.Prime p) (hp1 : 3 ≤ p) :
    (1 / 2) - ( (∑ k in Finset.Icc 1 ((p - 1) / 2), k ^ 120) / p ) % 1 = 1 / 2 := by
  norm_num
  <;> try { simp_all [Nat.mod_self] }
  <;> try { omega }