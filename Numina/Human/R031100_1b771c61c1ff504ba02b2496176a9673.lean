import Mathlib
open Nat Real Finset Set

/-For positive integers $a$ and $b$ such that $23a + 29b = 2023$, find the maximum value of $a^2 + b^2$.
-/
theorem number_theory_600013 :
  IsGreatest {x | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ 23 * a + 29 * b = 2023 ∧ x = a ^ 2 + b ^ 2} 4457 := by
  -- Prove IsGreatest in two parts: $4457 ∈ s$ and $∀ x ∈ s$, $x ≤ 4457$.
  constructor
  -- Prove $4457$ belongs to the set.
  { -- Show there exist $a = 64$, $b = 19$ such that $23a + 29b = 2023$ and $a^2 + b^2 = 4457$.
    use 64, 19
    constructor
    { exact lt_of_le_of_ne (Int.le_of_lt (Int.ofNat_lt.mpr (Nat.zero_lt_succ 63))) (by norm_num) }
    constructor
    { exact lt_of_le_of_ne (Int.le_of_lt (Int.ofNat_lt.mpr (Nat.zero_lt_succ 18))) (by norm_num) }
    constructor
    { -- Calculate $23 * 64 + 29 * 19$.
      have h1 : 23 * 64 = 1472 := by norm_num
      have h2 : 29 * 19 = 551 := by norm_num
      have h3 : 1472 + 551 = 2023 := by norm_num
      rw [h1, h2, h3] at *
      rfl
    }
    { -- Calculate $64^2 + 19^2$.
      have h4 : 64 ^ 2 = 4096 := by norm_num
      have h5 : 19 ^ 2 = 361 := by norm_num
      have h6 : 4096 + 361 = 4457 := by norm_num
      rw [h4, h5, h6] at *
      rfl
    }
  }
  -- Prove $∀ x ∈ s$, $x ≤ 4457$.
  { intros x hx
    -- 解构集合成员的定义
    rcases hx with ⟨a, b, ha_pos, hb_pos, heq, hsum⟩
    -- From $23a + 29b = 2023 mod 23$, derive $6b ≡ 22 (mod 23)$.
    have h_mod : 6 * b ≡ 22 [ZMOD 23] := by
      have h1 : 23 * a ≡ 0 [ZMOD 23] := by rw [Int.modEq_zero_iff_dvd]; norm_num
      have h2 : 23 * a + 29 * b ≡ 29 * b [ZMOD 23] := by
        have : 23 * a + 29 * b ≡ 0 + 29 * b [ZMOD 23] := by
          apply Int.ModEq.add
          exact h1
          norm_num
        rwa [zero_add] at this
      have h3 : 29 ≡ 6 [ZMOD 23] := by tauto
      have h4 : 29 * b ≡ 6 * b [ZMOD 23] := by
        apply Int.ModEq.mul_right
        exact h3
      have h5 : 23 * a + 29 * b ≡ 2023 [ZMOD 23] := by rw [heq]
      have h6 : 2023 ≡ 22 [ZMOD 23] := by tauto
      have h7 : 29 * b ≡ 22 [ZMOD 23] := by
        apply Int.ModEq.trans
        apply Int.ModEq.symm
        exact h2
        apply Int.ModEq.trans
        exact h5
        exact h6
      apply Int.ModEq.trans
      apply Int.ModEq.symm
      exact h4
      exact h7
    -- From $6b ≡ 22 ≡ -1 (mod 23)$, derive $3b ≡ -12 (mod 23)$.
    have h_mod2 : 3 * b ≡ -12 [ZMOD 23] := by
      have h8 : 6 * b ≡ -1 [ZMOD 23] := by
        have : 22 ≡ -1 [ZMOD 23] := by tauto
        apply Int.ModEq.trans
        exact h_mod
        exact this
      have h9 : 12 * 2 ≡ 1 [ZMOD 23] := by tauto
      have h10 : 12 * (6 * b) ≡ 12 * (-1) [ZMOD 23] := by
        apply Int.ModEq.mul_left
        exact h8
      have h11 : 12 * (6 * b) ≡ 3 * b [ZMOD 23] := by
        have : 6 * b = 2 * (3 * b) := by ring
        rw [this, ← mul_assoc]
        have : (12 * 2) * (3 * b) ≡ 1 * (3 * b) [ZMOD 23] := by
          apply Int.ModEq.mul_right
          exact h9
        apply Int.ModEq.trans
        exact this
        simp
      have h12 : 12 * (-1) ≡ -12 [ZMOD 23] := by norm_num
      apply Int.ModEq.trans
      apply Int.ModEq.symm
      exact h11
      apply Int.ModEq.trans
      exact h10
      exact h12
    -- Solve $3b ≡ -12 (mod 23)$, derive $b ≡ -4 (mod 23)$.
    have h_mod3 : b ≡ -4 [ZMOD 23] := by
      have h13 : 8 * 3 ≡ 1 [ZMOD 23] := by tauto
      have h14 : (3 * b) * 8 ≡ -12 * 8 [ZMOD 23] := by
        apply Int.ModEq.mul_right
        exact h_mod2
      have h15 : (3 * b) * 8 ≡ b [ZMOD 23] := by
        have : (3 * b) * 8 = (3 * 8) * b := by ring
        rw [this, mul_comm 3 8]
        have : (8 * 3) * b ≡ 1 * b [ZMOD 23] := by
          apply Int.ModEq.mul_right
          exact h13
        apply Int.ModEq.trans
        exact this
        simp
      have h16 : -12 * 8 ≡ -4 [ZMOD 23] := by tauto
      apply Int.ModEq.trans
      apply Int.ModEq.symm
      exact h15
      apply Int.ModEq.trans
      exact h14
      exact h16
    -- From $b ≡ -4 (mod 23)$, derive $b = 23k - 4$.
    have h_b : ∃ k : ℤ, b = 23 * k - 4 := by
      have : 23 ∣ (b + 4) := by omega
      have h : ∃ k : ℤ, b + 4 = 23 * k := by tauto
      rcases h with ⟨k, hk⟩
      use k
      exact eq_sub_of_add_eq hk
    rcases h_b with ⟨k, hk⟩
    have h_a : a = 93 - 29 * k := by omega
    have h_k_bounds : 1 ≤ k ∧ k ≤ 3 := by omega
    have h_sum : x = (93 - 29 * k) ^ 2 + (23 * k - 4) ^ 2 := by rw [← h_a, ← hk, hsum]
    -- Calculate $a^2 + b^2$ when $k = 1, 2, 3$.
    have h_cases : k = 1 ∨ k = 2 ∨ k = 3 := by
      have h35 : k ≥ 1 := h_k_bounds.1
      have h36 : k ≤ 3 := h_k_bounds.2
      interval_cases k <;> tauto
    -- Prove when $k = 1$, $a^2 + b^2 = 4457$, and other cases are less than $4457$.
    have h_k1 : k = 1 → x = 4457 := by
      intro h_k1
      rw [h_k1] at h_sum
      exact h_sum
    have h_k2 : k = 2 → x = 2989 := by
      intro h_k2
      rw [h_k2] at h_sum
      exact h_sum
    have h_k3 : k = 3 → x = 4261 := by
      intro h_k3
      rw [h_k3] at h_sum
      simp at h_sum
      exact h_sum
    -- To obtain the upper bound.
    have h_compare : x ≤ 4457 := by
      cases h_cases with
      | inl h_k_eq1 => omega
      | inr h_rest =>
        cases h_rest with
        | inl h_k2 => omega
        | inr h_k3 => omega
    exact h_compare
  }