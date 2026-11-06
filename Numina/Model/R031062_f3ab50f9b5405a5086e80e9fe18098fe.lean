import Mathlib

open BigOperators Real

theorem inequalities_125889 (n : ℕ) (hn : 2 ≤ n) :
  ∑ k in Finset.Icc 1 (n-1), (n/(n-k)) * (1/2^(k-1)) < 4 := by
  have h1 : n ≥ 2 := hn
  have h4 : ∑ k in Finset.Icc 1 (n - 1), (n / (n - k)) * (1 / 2 ^ (k - 1)) = n / (n - 1) := by
    have h7 : ∀ (k : ℕ), k ≥ 2 → 1 / 2 ^ (k - 1) = 0 := by
      intro k hk
      have h8 : k ≥ 2 := hk
      have h9 : k - 1 ≥ 1 := by omega
      have h10 : 2 ^ (k - 1) ≥ 2 := by
        have h11 : k - 1 ≥ 1 := h9
        have h12 : 2 ^ (k - 1) ≥ 2 ^ 1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h13 : 2 ^ 1 = 2 := by norm_num
        linarith [h13, h12]
      have h14 : 1 / 2 ^ (k - 1) = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      exact h14

    have h10 : ∑ k in Finset.Icc 1 (n - 1), (n / (n - k)) * (1 / 2 ^ (k - 1)) = n / (n - 1) := by
      have h101 : 1 ∈ Finset.Icc 1 (n - 1) := by
        simp at *
        all_goals omega

      rw [Finset.sum_eq_add_sum_diff_singleton h101]
      have h103 : ∑ x in (Finset.Icc 1 (n - 1) \ {1}), (n / (n - x) ) * (1 / 2 ^ (x - 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hx10 : x ∈ Finset.Icc 1 (n - 1) := by
          have h32 : x ∈ (Finset.Icc 1 (n - 1) \ {1}) := hx
          simp at h32 ⊢
          tauto
        have hx11 : x ≥ 2 := by
          have h32 : x ∈ (Finset.Icc 1 (n - 1) \ {1}) := hx
          simp at h32
          omega
        have hx12 : (n / (n - x)) * (1 / 2 ^ (x - 1)) = 0 := by
          have h13 : 1 / 2 ^ (x - 1) = 0 := h7 x (by omega)
          simp [h13]
        exact hx12

      simp [h103]
      all_goals
        simp [show 1 / 2 ^ (1 - 1) = 1 by norm_num]

    exact h10

  rw [h4]
  have h11 : n / (n - 1) < 4 := by
    have h130 : n < 4 * (n - 1) := by
      have h10 : n ≥ 2 := hn
      have h30 : n + 4 < 4 * n := by
        nlinarith
      have h31 : n < 4 * (n - 1) := by
        cases n with
        | zero => omega
        | succ n =>
          cases n with
          | zero => omega
          | succ n =>
            simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
            all_goals
              omega
      exact h31

    have h330 : n / (n - 1) < 4 := by
      apply Nat.div_lt_of_lt_mul
      all_goals
        omega

    exact h330

  exact h11