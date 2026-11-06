import Mathlib

theorem algebra_121533 {x : ℝ} (hx : x ≠ 0) (h : ∃ n : ℤ, x + 1 / x = n) :
    ∀ n : ℕ, ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
  intro n 
  have h1 : ∃ n : ℤ, x + 1 / x = n := h 
  rcases h1 with ⟨k, hk⟩
  have h2 : ∀ n : ℕ, ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
    intro n
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      use 2
      norm_num 
      <;> field_simp [hx] at hk ⊢ 
      <;> linarith 
    | succ n =>
      cases n with 
      | zero =>
        use k 
        field_simp [hx] at hk ⊢ 
        linarith 
      | succ n =>
        rcases ih (n) (by linarith) with ⟨m1, hm1⟩
        rcases ih (n + 1) (by linarith) with ⟨m2, hm2⟩
        use (k * m2 - m1)
        have eq1 : x ^ (n + 2 : ℕ) + 1 / x ^ (n + 2 : ℕ) = (x + 1 / x) * (x ^ (n + 1 : ℕ) + 1 / x ^ (n + 1 : ℕ)) - (x ^ (n : ℕ) + 1 / x ^ (n : ℕ)) := by
          field_simp [hx]
          <;> ring 
        rw [eq1]
        rw [hm1]
        rw [hm2]
        rw [hk]
        all_goals norm_num 
        <;> ring 
  specialize h2 n 
  simpa using h2