import Mathlib

theorem algebra_195142 {n f : ℕ} (hn : n > 0) (hf : f > 0)
    (h : n * f = n + f + 30) : n * f = 64 := by
  have h1 : n * f = n + f + 30 := h
  -- Let's derive (n - 1) * (f - 1) = 31 algebraically.
  -- n * f -n -f +1 = 31
  have eq1 : (n - 1) * (f - 1) = 31 := by
    have eq2 : n * f = n + f + 30 := h
    cases n with
    | zero =>
      linarith
    | succ n =>
      cases f with
      | zero =>
        linarith
      | succ f =>
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at eq2 ⊢
        all_goals
          ring_nf at eq2 ⊢
          omega
  have h3 : (n - 1) = 1 ∨ (n - 1) = 31 := by
    have h4 : (n - 1) ∣ (n - 1) * (f - 1) := by
      use (f - 1)
      all_goals
        ring_nf
    have h5 : (n - 1) ∣ 31 := by
      rw [eq1] at h4
      exact h4
    have h6 : (n - 1) = 1 ∨ (n - 1) = 31 := by
      have h7 : (n - 1) ≤ 31 := by
        exact Nat.le_of_dvd (by norm_num) h5
      interval_cases (n - 1) <;> omega
    exact h6
  rcases h3 with (h4 | h4)
  · -- Case where n - 1 = 1, so n = 2, then f = 32
    have hn2 : n = 2 := by
      omega
    have hf32 : f = 32 := by
      nlinarith [eq1, hn2]
    calc
      n * f = 2 * 32 := by rw [hn2, hf32]
      _ = 64 := by norm_num
  · -- Case where n - 1 = 31, so n = 32, then f = 2
    have hn32 : n = 32 := by
      omega
    have hf2 : f = 2 := by
      nlinarith [eq1, hn32]
    calc
      n * f = 32 * 2 := by rw [hn32, hf2]
      _ = 64 := by norm_num