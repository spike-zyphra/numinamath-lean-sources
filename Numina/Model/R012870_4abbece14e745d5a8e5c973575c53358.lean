import Mathlib

theorem algebra_298309 {a : ℕ → ℤ}
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 2 * a n + n * (1 + 2 ^ n)) :
    ∀ n ≥ 2, a n = 2 ^ (n - 2) * (n ^ 2 - n + 6) - n - 1 := by
  intro n hn 
  have h2 : n ≥ 2 := hn 
  have h3 : a 2 = 5 := by 
    have eq1 : a 2 = 2 * a 1 + 1 * (1 + 2^1) := by 
      specialize han 1 (by norm_num)
      simpa using han 
    rw [ha1] at eq1 
    norm_num at eq1 ⊢ 
    linarith 
  have h4 : ∀ (k : ℕ), a (k + 2) = 2 ^ (k + 2 - 2) * ((↑k + 2) ^ 2 - (↑k + 2) + 6) - (↑k + 2) - 1 := by 
    intro k 
    induction k with 
    | zero => 
      simpa using h3 
    | succ k ih => 
      have h5 : a ((k + 1) + 2) = 2 * a (k + 2) + (k + 2) * (1 + 2 ^ (k + 2)) := by 
        specialize han (k + 2) (by linarith)
        simpa using han 
      rw [h5] 
      rw [ih]
      cases k with 
      | zero => 
        all_goals
          norm_num 
      | succ k => 
        simp [pow_two, pow_succ, mul_add, mul_comm] at *
        all_goals 
          ring_nf 
          <;> omega 
  have hn2 : n ≥ 2 := by linarith 
  have h5 : a n = 2 ^ (n - 2) * (n ^ 2 - n + 6) - n - 1 := by 
    have h9 : a (n - 2 + 2) = 2 ^ ((n - 2 + 2) - 2) * ((↑(n - 2) + 2) ^ 2 - (↑(n - 2) + 2) + 6) - (↑(n - 2) + 2) - 1 := by 
      specialize h4 (n - 2)
      simpa using h4 
    have h6 : n - 2 + 2 = n := by omega 
    rw [h6] at h9 
    have h7 : a n = 2 ^ (n - 2) * ((↑(n - 2) + 2) ^ 2 - (↑(n - 2) + 2) + 6) - (↑(n - 2) + 2) - 1 := h9 
    rw [h7] 
    cases n with 
    | zero => 
      linarith 
    | succ n => 
      cases n with 
      | zero => 
        linarith 
      | succ n => 
        simp [pow_two, pow_succ, mul_add, mul_comm] at *
        all_goals 
          ring 
  exact h5