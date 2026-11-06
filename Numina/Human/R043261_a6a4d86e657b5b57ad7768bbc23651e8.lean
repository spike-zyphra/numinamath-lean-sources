import Mathlib

theorem number_theory_320993 :
    IsGreatest {n : ℕ | 2 ^ n ∣ 2007 ^ 2048 - 1} 14 := by
  constructor
  . native_decide
  . intro n hn
    by_contra! h
    have k : 2 ^ 15 ∣ 2007 ^ 2048 - 1 := (Nat.pow_dvd_pow _ h).trans hn
    absurd k
    native_decide
