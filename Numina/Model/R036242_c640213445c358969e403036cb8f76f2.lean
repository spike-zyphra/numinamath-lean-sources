import Mathlib


theorem Number_theory_241485 (a k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (h : a^2 + k ∣ (a - 1) * a * (a + 1)) : k ≥ a := by
  by_contra h1
  push_neg at h1
  -- Now, we need to derive a contradiction from h. Let's write some algebra:
  -- We need to show that $a^2 + k$ divides `a \cdot (k + 1)` from the given h.
  -- From h: ` a^2 + k ∣ (a - 1) * a * (a + 1) `.
  -- From h expand: ` a^2 + k ∣ a * (a^2 + k) `.
  -- Therefore, ` a^2 + k ∣ a * (a^2 + k) - (a - 1) * a * (a + 1) `.
  -- The result is ` a \cdot (k+1) `.
  have h3 : a ^ 2 + k ∣ a * (k + 1) := by
    have h5 : a ^ 2 + k ∣ a * (a ^ 2 + k) := by
      use a
      all_goals ring_nf
    have h10 : a ^ 2 + k ∣ a * (a ^ 2 + k) - ((a - 1) * a * (a + 1)) := by
      apply Nat.dvd_sub'
      exact h5
      exact h
    have eq2 : a * (a ^ 2 + k) - ((a - 1) * a * (a + 1)) = a * (k + 1) := by
      cases a with
      | zero =>
        exfalso
        linarith
      | succ a =>
        simp [Nat.mul_add, Nat.add_mul, mul_add, mul_assoc, Nat.mul_sub_left_distrib, Nat.add_sub_cancel]
        all_goals
          ring_nf
          <;> omega
    rw [eq2] at h10
    exact h10
  -- We have proven h3 : a^2 + k divides a * (k + 1).
  have h4 : a ^ 2 + k ≤ a * (k + 1) := by
    exact Nat.le_of_dvd (by nlinarith [show 0 < a by linarith, show 0 < k by linarith]) h3
  -- But since k < a, we need to show that a * (k + 1) < a^2 + k.
  have h12 : a * (k + 1) < a ^ 2 + k := by
    have h13 : k < a := by
      omega
    -- We can show that a * (k + 1) < a^2 + k when k < a
    nlinarith [sq_pos_of_pos (show 0 < a by linarith), sq_nonneg (k : ℕ), sq_nonneg (a - 1 : ℕ), sq_nonneg (k - a : ℤ)]
  -- Contradicts with h4 and h12
  nlinarith