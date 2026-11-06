import Mathlib

theorem number_theory_112326 (n : ℕ) : 25 ∣ 2^(n + 2) * 3^n + 5 * n - 4 := by
  have h1 : ∀ (n : ℕ), 25 ∣ 2 ^ (n + 2) * 3 ^ n + 5 * n - 4 := by
    intro n
    induction n with
    | zero =>
      norm_num
      <;> omega
    | succ k ih =>
      have eq1 : (2 ^ ((k + 1 : ℕ) + 2) * 3 ^ (k + 1) + 5 * (k + 1) - 4 : ℕ) 
        = (6 * (2 ^ (k + 2) * 3 ^ k) + 5 * k + 1) := by
        ring_nf
        <;> omega
      rw [eq1]
      have h4 : 25 ∣ 6 * (2 ^ (k + 2) * 3 ^ k) + 5 * k + 1 := by
        rcases ih with ⟨m, hm⟩
        -- From `ih`, we have `2 ^ (k + 2) * 3 ^ k + 5 * k - 4 = 25 * m`
        -- We need to show `6 * (2 ^ (k + 2) * 3 ^ k) + 5 * k + 1` is divisible by 25
        use 6 * m - k + 1
        cases k with
        | zero =>
          simp [Nat.mul_zero, Nat.mul_assoc, pow_zero] at hm ⊢
          <;> omega
        | succ k =>
          simp [Nat.mul_succ, pow_succ] at hm ⊢
          all_goals
          omega
      assumption
  specialize h1 n
  simpa using h1