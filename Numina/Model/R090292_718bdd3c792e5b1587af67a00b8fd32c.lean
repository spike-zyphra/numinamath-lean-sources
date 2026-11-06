import Mathlib

theorem number_theory_238878 {n : ℕ} (h : n < 100) (h' : n > 9)
    (h'' : n / (Nat.ofDigits 10 [n % 10, n / 10]) = n % (Nat.ofDigits 10 [n % 10, n / 10])) :
    n = 52 := by 
  interval_cases n <;> norm_num [Nat.ofDigits, List.foldl] at h'' <;> omega