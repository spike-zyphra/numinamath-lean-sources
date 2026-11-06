import Mathlib
open Finset Set Nat  
noncomputable section

/-14.59 Find all natural numbers $n$ such that $\min _{k \in N}\left(k^{2}+\left[\frac{n}{k^{2}}\right]\right)=1991$, where $N$ is the set of natural numbers.
(6th China High School Mathematics Winter Camp, 1991)-/
theorem number_theory_609999 :
    ∀ n : ℕ, (n > 0 ∧ ∃ k : ℕ, k > 0 ∧ k^2 + n / k^2 = 1991 ∧
      ∀ m : ℕ, m > 0 → k^2 + n / k^2 ≤ m^2 + n / m^2) ↔
    1024 * 967 ≤ n ∧ n < 1024 * 968 := by
  intro n
  constructor
  · -- Forward implication: If there exists $k$ such that the condition holds, then $n$ must be in the specified range.
    intro h_cond
    have h_n_pos : n > 0 := h_cond.1
    have h_k_exists : ∃ k : ℕ, k > 0 ∧ k^2 + n / k^2 = 1991 ∧ ∀ m : ℕ, m > 0 → k^2 + n / k^2 ≤ m^2 + n / m^2 := h_cond.2
    rcases h_k_exists with ⟨k, h_k_pos, h_k_eq_1991, h_k_min⟩
    have h_n_ge_1024_967 : 1024 * 967 ≤ n := by
      by_contra h_n_not_ge_1024_967
      -- Assume $n < 1024 * 967$.
      have h_n_lt_1024_967 : n < 1024 * 967 := by omega
      have h_k_eq_1991_lower : k^2 + n / k^2 = 1991 := h_k_eq_1991
      have h_k_min_lower : ∀ m : ℕ, m > 0 → k^2 + n / k^2 ≤ m^2 + n / m^2 := h_k_min
      have h_k_self_min := h_k_min_lower k h_k_pos
      have h_m1_min := h_k_min_lower 1 (by norm_num)
      have h_m32_min := h_k_min_lower 32 (by norm_num)
      have h_k_le_44 : k ≤ 44 := by
        by_contra h_k_not_le_44
        have h_k_ge_45 : k ≥ 45 := by omega
        have h_k2_ge_2025 : k^2 ≥ 2025 := by nlinarith
        have h_n_div_k2_eq_0 : n / k^2 = 0 := by
          have h_n_lt_1024_967_bound : n < 1024 * 967 := h_n_lt_1024_967
          have h_k2_ge_2025_bound : k^2 ≥ 2025 := h_k2_ge_2025
          have h_n_lt_k2 : n < k^2 := by
            omega
          have h_n_div_k2_zero : n / k^2 = 0 := by
            apply Nat.div_eq_of_lt
            nlinarith
          exact h_n_div_k2_zero
        have h_k2_ge_2025_sum : k^2 + n / k^2 ≥ 2025 := by
          omega
        omega
      interval_cases k <;> norm_num at h_k_eq_1991_lower ⊢ <;>
        omega
    have h_n_lt_1024_968 : n < 1024 * 968 := by
      by_contra h_n_not_lt_1024_968
      -- Assume $n ≥ 1024 * 968$.
      have h_n_ge_1024_968 : n ≥ 1024 * 968 := by omega
      have h_k_eq_1991_upper : k^2 + n / k^2 = 1991 := h_k_eq_1991
      have h_k_min_upper : ∀ m : ℕ, m > 0 → k^2 + n / k^2 ≤ m^2 + n / m^2 := h_k_min
      have h_k_self_min_upper := h_k_min_upper k h_k_pos
      have h_m1_min_upper := h_k_min_upper 1 (by norm_num)
      have h_m32_min_upper := h_k_min_upper 32 (by norm_num)
      have h_k_le_44_upper : k ≤ 44 := by
        by_contra h_k_not_le_44_upper
        have h_k_ge_45_upper : k ≥ 45 := by omega
        have h_k2_ge_2025_upper : k^2 ≥ 2025 := by nlinarith
        have h_n_div_k2_ge_0 : 0 ≤ n / k^2 := by
          apply Nat.zero_le
        have h_k2_sum_ge_2025 : k^2 + n / k^2 ≥ 2025 := by nlinarith
        linarith
      interval_cases k <;> norm_num at h_k_eq_1991_upper ⊢ <;>
        omega
    exact ⟨h_n_ge_1024_967, h_n_lt_1024_968⟩
  · -- Reverse implication: If $n$ is in the specified range, then there exists $k$ such that the condition holds.
    intro h_bounds
    have h_n_ge_1024_967 : 1024 * 967 ≤ n := h_bounds.1
    have h_n_lt_1024_968 : n < 1024 * 968 := h_bounds.2
    have h_n_pos : n > 0 := by
      omega
    have h_k_32_exists : ∃ k : ℕ, k > 0 ∧ k^2 + n / k^2 = 1991 ∧ ∀ m : ℕ, m > 0 → k^2 + n / k^2 ≤ m^2 + n / m^2 := by
      use 32
      constructor
      · -- Prove $32 > 0$.
        norm_num
      · constructor
        · -- Prove $32^2 + n / 32^2 = 1991$.
          have h_n_lt_1024_968_bound : n < 1024 * 968 := h_n_lt_1024_968
          have h_n_ge_1024_967_bound : 1024 * 967 ≤ n := h_n_ge_1024_967
          have h_n_div_1024_eq_967 : n / 1024 = 967 := by
            have h_n_ge_1024_967_bound2 : 1024 * 967 ≤ n := h_n_ge_1024_967
            have h_n_lt_1024_968_bound2 : n < 1024 * 968 := h_n_lt_1024_968
            have h_n_div_1024_eq_967_bound : n / 1024 = 967 := by
              omega
            exact h_n_div_1024_eq_967_bound
          have h_n_div_32_eq_967 : n / (32 ^ 2) = 967 := by
            have h_32_sq_eq_1024 : 32 ^ 2 = 1024 := by norm_num
            rw [h_32_sq_eq_1024]
            exact h_n_div_1024_eq_967
          norm_num [h_n_div_32_eq_967]
          omega
        · -- Prove $∀ m > 0$, $32^2 + n / 32^2 ≤ m^2 + n / m^2$.
          intro m h_m_pos
          have h_n_lt_1024_968_bound2 : n < 1024 * 968 := h_n_lt_1024_968
          have h_n_ge_1024_967_bound2 : 1024 * 967 ≤ n := h_n_ge_1024_967
          have h_n_div_1024_eq_967_2 : n / 1024 = 967 := by
            have h_n_ge_1024_967_bound3 : 1024 * 967 ≤ n := h_n_ge_1024_967
            have h_n_lt_1024_968_bound3 : n < 1024 * 968 := h_n_lt_1024_968
            have h_n_div_1024_eq_967_bound2 : n / 1024 = 967 := by
              omega
            exact h_n_div_1024_eq_967_bound2
          have h_n_div_32_eq_967_2 : n / (32 ^ 2) = 967 := by
            have h_32_sq_eq_1024_2 : 32 ^ 2 = 1024 := by norm_num
            rw [h_32_sq_eq_1024_2]
            exact h_n_div_1024_eq_967_2
          have h_k32_eq_1991 : 32 ^ 2 + n / (32 ^ 2) = 1991 := by
            norm_num [h_n_div_32_eq_967_2]
            omega
          have h_k32_min : 32 ^ 2 + n / (32 ^ 2) ≤ m ^ 2 + n / m ^ 2 := by
            by_cases h_m_le_44 : m ≤ 44
            · -- When $m ≤ 44$.
              interval_cases m <;> norm_num at h_m_pos ⊢ <;>
                omega
            · -- When $m > 44$.
              have h_m_ge_45 : m ≥ 45 := by omega
              have h_m2_ge_2025 : m ^ 2 ≥ 2025 := by nlinarith
              have h_n_div_m2_ge_0 : n / m ^ 2 ≥ 0 := by
                apply Nat.zero_le
              have h_m2_ge_2025_sum : m ^ 2 + n / m ^ 2 ≥ 2025 := by
                omega
              have h_k32_eq_1991_bound : 32 ^ 2 + n / (32 ^ 2) = 1991 := h_k32_eq_1991
              have h_m_min_1991 : 1991 ≤ m ^ 2 + n / m ^ 2 := by
                omega
              omega
          exact h_k32_min
    exact ⟨h_n_pos, h_k_32_exists⟩
