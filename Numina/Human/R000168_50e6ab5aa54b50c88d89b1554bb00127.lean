import Mathlib

theorem number_theory_7732 (a b : ℤ) (h : 21 ∣ a^2 + b^2) : 441 ∣ a^2 + b^2 := by
  apply IsCoprime.mul_dvd (show IsCoprime (3 ^ 2 : ℤ) (7 ^ 2) by norm_num)
  . have k := legendreSym.prime_dvd_of_eq_neg_one (p := 3) (a := -1) (by native_decide) (x := a) (y := b)
    simp at k
    specialize k (dvd_trans (show 3 ∣ 21 by norm_num) h)
    exact dvd_add (pow_dvd_pow_of_dvd k.1 2) (pow_dvd_pow_of_dvd k.2 2)
  . have k := @legendreSym.prime_dvd_of_eq_neg_one 7 { out := by norm_num } (-1) (by native_decide) a b
    simp at k
    specialize k (dvd_trans (show 7 ∣ 21 by norm_num) h)
    exact dvd_add (pow_dvd_pow_of_dvd k.1 2) (pow_dvd_pow_of_dvd k.2 2)