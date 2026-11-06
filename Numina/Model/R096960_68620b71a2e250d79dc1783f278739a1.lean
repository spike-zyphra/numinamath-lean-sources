import Mathlib

theorem number_theory_109318 {n : ℕ} (hn : n * 100 + 99 ∣ 20083) :
    n = 17 ∨ n = 117 := by
  have h1 : n * 100 + 99 ≤ 20083 := by
    exact Nat.le_of_dvd (by norm_num) hn
  have h2 : n ≤ 199 := by
    omega
  interval_cases n <;> omega