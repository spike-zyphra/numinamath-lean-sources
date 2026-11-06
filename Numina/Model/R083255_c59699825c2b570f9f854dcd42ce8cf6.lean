import Mathlib

theorem number_theory_173032 {n : ℕ} (hn : n > 229) (h : n % 99 + n % 132 + n % 229 = n) :
    n % 99 + n % 132 = 229 := by
  have h1 : n % 99 < 99 := by
    apply Nat.mod_lt
    all_goals omega
  have h2 : n % 132 < 132 := by
    apply Nat.mod_lt
    all_goals omega
  have h3 : n % 229 < 229 := by
    apply Nat.mod_lt
    all_goals omega
  omega