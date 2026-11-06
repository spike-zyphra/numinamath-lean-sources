import Mathlib

theorem algebra_180988 {a : ℕ → ℝ} (ha0 : a 0 = 2)
    (han : ∀ n ≥ 1, a n = (2 * a (n - 1) + 6) / (a (n - 1) + 1)) :
    ∀ n, a n = (3 * 4^(n + 1) + 2 * (-1)^(n + 1)) / (4^(n + 1) + (-1)^n) := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    -- Base case: n = 0
    rw [ha0]
    norm_num
  | succ k =>
    -- Inductive step: Assume it holds for k, prove for k + 1
    have h1 := ih k (by linarith)
    have h2 : a (k + 1) = (2 * a k + 6) / (a k + 1) := by
      specialize han (k + 1) (by linarith)
      simpa using han
    rw [h2, h1]
    have h9 : (4 : ℝ) ^ (k + 1) + (-1 : ℝ) ^ k ≠ 0 := by 
      have h11 : (4 : ℝ) ^ (k + 1) ≥ 4 := by 
        have h1111 : (4 : ℝ) ^ (k + 1) ≥ (4 : ℝ) := by
          have h15 : (4 : ℝ) ^ (k + 1) ≥ (4 : ℝ) ^ 1 := by
            apply pow_le_pow_right 
            all_goals norm_num 
          have h17 : (4 : ℝ) ^ 1 = (4 : ℝ) := by norm_num 
          rw [h17] at h15 
          linarith 
        linarith
      have h12 : (4 : ℝ) ^ (k + 1) + (-1 : ℝ) ^ k ≥ 3 := by
        have h99 : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := by 
          have h100 : ∀ (n : ℕ), (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
            intro n
            induction n with
            | zero => 
              norm_num 
            | succ n ih =>
              rw [show (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) * (-1) ^ n by ring]
              cases ih with 
              | inl h => 
                rw [h]
                norm_num 
              | inr h => 
                rw [h]
                norm_num 
          exact h100 k 
        cases h99 with
        | inl h99 => 
          rw [h99] 
          have h101 : (4 : ℝ) ^ (k + 1) ≥ 4 := h11 
          linarith 
        | inr h99 => 
          rw [h99] 
          have h101 : (4 : ℝ) ^ (k + 1) ≥ 4 := h11 
          linarith 
      intro h 
      have h10 : (4 : ℝ) ^ (k + 1) + (-1 : ℝ) ^ k = 0 := by 
        linarith 
      nlinarith 
    field_simp [h9]
    ring_nf