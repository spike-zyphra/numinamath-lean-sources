import Mathlib

theorem number_theory_172778 {n : ℕ} (hn : n > 229) :
    (n % 99 + n % 132 + n % 229 = n) ↔ n = 395 := by
  constructor
  · -- Forward direction: assuming n % 99 + n % 132 + n % 229 = n, prove n = 395
    intro h
    have h1 : n < 460 := by
      have h1 : n % 99 < 99 := by apply Nat.mod_lt; omega
      have h2 : n % 132 < 132 := by apply Nat.mod_lt; omega
      have h3 : n % 229 < 229 := by apply Nat.mod_lt; omega
      linarith 
    interval_cases n <;> omega
  · -- Backward direction: assuming n = 395, prove n % 99 + n % 132 + n % 229 = n
    intro h
    subst h
    all_goals norm_num