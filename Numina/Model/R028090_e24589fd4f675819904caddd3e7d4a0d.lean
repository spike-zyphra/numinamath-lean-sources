import Mathlib

theorem number_theory_155817 (n : ℕ) : ¬(Even (Nat.fib n) ∧ Even (Nat.fib (n + 1))) := by
  have h1 : ∀ n : ℕ, ¬(Even (Nat.fib n) ∧ Even (Nat.fib (n + 1))) := by
    intro n 
    induction n with
    | zero => 
      have h1 : Nat.fib 0 = 0 := by 
        simp [Nat.fib_zero]
      have h2 : Nat.fib 1 = 1 := by 
        simp [Nat.fib_one]
      simp [h1, h2, Nat.even_iff]
      all_goals norm_num 
    | succ k ih => 
      by_contra h 
      rcases h with ⟨h1, h2⟩ 
      have heven1 : Even (Nat.fib (k + 1)) := h1 
      have heven2 : Even (Nat.fib (k + 2)) := by 
        have : Nat.fib (k + 1 + 1) = Nat.fib (k + 2) := by 
          simp 
        rw [this] at h2 
        exact_mod_cast h2
      have heven3 : Even (Nat.fib k) := by 
        have eq1 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by 
          simp [Nat.fib_add_two]
          <;> ring_nf
        rcases heven1 with ⟨m, hm⟩ 
        rcases heven2 with ⟨n, hn⟩
        have : Nat.fib k = 2 * (n - m) := by
          omega 
        rw [this] 
        exact ⟨n - m, by ring⟩ 
      have h5 : Even (Nat.fib k) ∧ Even (Nat.fib (k + 1)) := by 
        constructor 
        · exact_mod_cast heven3 
        · exact_mod_cast heven1 
      have h6 : ¬(Even (Nat.fib k) ∧ Even (Nat.fib (k + 1)) ) := ih 
      contradiction 
  specialize h1 n 
  simpa using h1