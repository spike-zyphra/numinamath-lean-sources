import Mathlib

theorem number_theory_6713 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 11 ∣ Nat.ofDigits 10 [9, b, 0, a, 1]) :
    Nat.ofDigits 10 [9, b, 0, a, 1] % 9 = 2 := by 
  interval_cases a <;> interval_cases b <;> norm_num [Nat.ofDigits] at h ⊢ <;> omega
  <;> try { trivial }