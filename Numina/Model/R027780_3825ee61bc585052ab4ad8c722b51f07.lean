import Mathlib

theorem number_theory_99977 (n : ℕ) (hn : n ≠ 0) :
    ∃ a b, 35^n = a^2 - b^2 := by
  have h1 : n > 0 := by
    by_contra h
    push_neg at h
    have h2 : n = 0 := by
      omega
    tauto
  have h2 : (35 : ℕ) % 2 = 1 := by norm_num
  have h3 : (35 ^ n : ℕ) % 2 = 1 := by
    have h7 : ∀ k : ℕ, (35 ^ k : ℕ) % 2 = 1 := by
      intro k 
      induction k with
      | zero => 
        simp
      | succ k ih =>
        simp [Nat.pow_succ, Nat.mul_mod, ih] 
    specialize h7 n
    simpa using h7
  have h7 : ∃ m : ℕ, (35 ^ n : ℕ) = 2 * m + 1 := by
    have h9 : (35 ^ n : ℕ) % 2 = 1 := h3
    have h10 : (35 ^ n : ℕ) ≥ 1 := by
      have h11 : n > 0 := h1
      have h12 : n ≥ 1 := by omega
      have h13 : (35 : ℕ) ^ n ≥ (35 : ℕ) ^ 1 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals
          omega
      have h14 : (35 : ℕ) ^ 1 = 35 := by norm_num
      rw [h14] at h13 
      have h15 : (35 : ℕ) ≥ 1 := by norm_num 
      linarith
    refine ⟨(35 ^ n - 1) / 2, by
      omega
    ⟩
  rcases h7 with ⟨m, hm⟩
  use m + 1, m
  rw [hm]
  cases m with 
  | zero =>
    all_goals
      norm_num
  | succ m =>
    simp [Nat.pow_succ, Nat.pow_zero, Nat.add_assoc, Nat.mul_add, Nat.add_mul]
    all_goals
      ring_nf
      <;> omega