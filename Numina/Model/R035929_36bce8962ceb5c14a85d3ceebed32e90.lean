import Mathlib

theorem number_theory_16112 {n : ℕ} (hn : n > 0) :
    ∏ d ∈ n.divisors, d = 729 ↔ n = 27 := by
  constructor
  · -- If ∏ d ∈ n.divisors, d = 729, then n = 27.
    intro h
    have h3 : n ∣ 729 := by
      have h4 : n ∣ ∏ d in n.divisors, d := by 
        have h5 : n ∈ n.divisors := by 
          have h5a : n ∣ n := by exact dvd_refl n
          have h10 : n ≠ 0 := by omega
          simp [Nat.mem_divisors, h5a, h10]
        apply Finset.dvd_prod_of_mem (fun x => x) h5
      have h9 : ∏ d in n.divisors, d = 729 := h
      rw [h9] at h4
      exact h4
    have h8 : n ≤ 729 := by 
      exact Nat.le_of_dvd (by linarith) h3
    have h7 : n ∣ 3 ^ 6 := by
      norm_num at h3 ⊢
      exact h3
    have h13 : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 ∨ n = 81 ∨ n = 243 ∨ n = 729 := by
      have h14 : n ∣ 3 ^ 6 := h7
      have h15 : n ≤ 3 ^ 6 := by
        exact Nat.le_of_dvd (by norm_num) h14
      interval_cases n <;> try { 
        norm_num at h14 ⊢ 
        <;> tauto 
      }
    rcases h13 with (r | r | r | r | r | r | r)
    · -- n = 1
      rw [show n = 1 by omega] at h
      have h1 : ∏ d in (1 : ℕ).divisors, d = 1 := by 
        native_decide
      rw [h1] at h
      all_goals
      omega
    · -- n = 3
      rw [show n = 3 by omega] at h
      have h1 : ∏ d in (3 : ℕ).divisors, d = 3 := by 
        native_decide
      rw [h1] at h
      all_goals
      omega
    · -- n = 9
      rw [show n = 9 by omega] at h
      have h1 : ∏ d in (9 : ℕ).divisors, d = 27 := by 
        native_decide
      rw [h1] at h
      all_goals
      omega
    · -- n = 27
      omega
    · -- n = 81
      rw [show n = 81 by omega] at h
      have h1 : ∏ d in (81 : ℕ).divisors, d = 59049 := by
        native_decide
      rw [h1] at h
      all_goals
      omega
    · -- n = 243
      rw [show n = 243 by omega] at h
      have h1 : ∏ d in (243 : ℕ).divisors, d = 14348907 := by
        native_decide
      rw [h1] at h
      all_goals
      omega
    · -- n = 729
      rw [show n = 729 by omega] at h
      have h1 : ∏ d in (729 : ℕ).divisors, d = 10460353203 := by
        native_decide
      rw [h1] at h
      all_goals
      omega
  · -- If n = 27, then ∏ d ∈ n.divisors, d = 729.
    intro h
    rw [show n = 27 by exact h]
    native_decide