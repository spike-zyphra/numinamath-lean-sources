import Mathlib

theorem number_theory_63666 (a k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (h : a ^ 2 + k ∣ (a - 1) * a * (a + 1)) : k ≥ a := by
  by_cases ha2 : a > 1
  · -- Assume a > 1
    have h1 : a ^ 2 + k ∣ (a - 1) * a * (a + 1) := h
    have h1' : a ^ 2 + k ∣ (a - 1) * a * (a + 1) := h1
    by_contra h9
    push_neg at h9
    -- We have k < a
    -- Assume k < a, to derive contradiction
    have h10 : k < a := h9
    -- k < a, so k ≤ a - 1
    have h11' : k ≤ a - 1 := by
      omega
    -- Establish the inequality from polynomial division
    have h2 : a ^ 2 + k ∣ a * (a ^ 2 + k) := by
      use a
      all_goals ring
    have h5 : a ^ 2 + k ∣ a * (a ^ 2 + k) - ( (a - 1) * a * (a + 1) ) := by
      apply Nat.dvd_sub'
      · exact h2
      · exact h1'
    have h10' : a * (a ^ 2 + k) - ( (a - 1) * a * (a + 1) ) = a + a * k := by
      cases a with
      | zero => linarith
      | succ a =>
        cases a with
        | zero => linarith
        | succ a => 
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.mul_assoc] at *
          <;> ring_nf at *
          <;> omega
    have h11 : a ^ 2 + k ∣ a + a * k := by
      have h8 : a ^ 2 + k ∣ a * (a ^ 2 + k) - ( (a - 1) * a * (a + 1) ) := h5
      rw [h10'] at h8
      exact h8
    -- Now from inequality
    have h12 : a ^ 2 + k ≤ a + a * k := by
      by_contra h13
      push_neg at h13
      -- Assume a ^ 2 + k > a + a * k
      have h14 : a ^ 2 + k > a + a * k := by nlinarith
      have h15 : a ^ 2 + k ∣ a + a * k := h11
      have h16 : a + a * k > 0 := by
        nlinarith
      -- Since a ^ 2 + k > a + a * k, it cannot divide it.
      have h17 : a ^ 2 + k ≤ a + a * k := by
        apply Nat.le_of_dvd (by linarith) h15
      linarith
    -- Contradicts since k < a
    nlinarith [sq_nonneg (a - k : ℤ), sq_nonneg ((a : ℤ) - 1), sq_nonneg ((k : ℤ) - (a : ℤ)), mul_pos (show (0 : ℕ) < a by linarith) (show (0 : ℕ) < k by linarith)]
  · -- If a ≤ 1, since a > 0, so a = 1
    have ha3 : a = 1 := by
      omega
    rw [ha3] at h
    norm_num at h
    all_goals
      omega