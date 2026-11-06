import Mathlib

theorem algebra_164075 {t : ℕ → ℝ} (ht1 : t 1 = 1) (hht : ∀ n > 1, Even n → t n = 1 + t (n / 2)) (hht' : ∀ n > 1, Odd n → t n = 1 / t (n - 1)) : ∃ n , t n = 19 / 87 ∧ (Nat.digits 10 n).sum = 15 := by 
  use 1905
  constructor
  · -- Show that t 1905 = 19 / 87
    norm_num [ht1, hht, hht', Nat.even_iff, Nat.odd_iff] at *
    all_goals norm_num [ht1, hht, hht', Nat.even_iff, Nat.odd_iff]
  · -- Show that digit sum is 15
    norm_num