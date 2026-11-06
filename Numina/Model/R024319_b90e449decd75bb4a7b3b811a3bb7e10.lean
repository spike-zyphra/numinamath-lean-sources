import Mathlib

theorem number_theory_5159 (n : ℕ) (hn : n ≥ 30) (h : 45 % n = 147 % n) (h' : 147 % n = 215 % n) :
    n = 34 := by
  by_cases h1 : n ≤ 215
  · -- Case n ≤ 215
    interval_cases n <;> omega
  · -- Case n > 215
    have h1' : 45 % n = 45 := by
      simp [Nat.mod_eq_of_lt, show 45 < n by linarith]
    have h1'' : 147 % n = 147 := by
      simp [Nat.mod_eq_of_lt, show 147 < n by linarith]
    have h1''' : 215 % n = 215 := by
      simp [Nat.mod_eq_of_lt, show 215 < n by linarith]
    rw [h1', h1''] at h
    omega