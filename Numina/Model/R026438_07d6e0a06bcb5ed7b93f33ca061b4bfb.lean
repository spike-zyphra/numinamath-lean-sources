import Mathlib

theorem number_theory_223518 {n : ℕ} (h : 61 ∣ Nat.factorial n + Nat.factorial (n+1) + Nat.factorial (n+2)) :
    n + 2 ≥ 61 := by
  by_contra h1
  push_neg at h1
  have h2 : n ≤ 58 := by 
    omega
  interval_cases n <;> try { contradiction }
  <;> norm_num [Nat.factorial] at h
  all_goals omega