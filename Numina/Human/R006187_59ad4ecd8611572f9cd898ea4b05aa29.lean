import Mathlib
open Finset Set 

/-Among the five-digit natural numbers, what is the smallest one that has no repeated digits and is divisible by $45$?-/
theorem number_theory_601111 :
  IsLeast {n : Nat | 10000 ≤ n ∧ n < 100000 ∧ (∃ k : Nat, n = 45 * k) ∧
    List.Nodup (Nat.digits 10 n)} 10395 := by
  constructor
  · -- Subgoal : Prove that 10395 satisfies the conditions.
    -- Verify that $45 × 231 = 10395$, a five-digit number with no repeated digits, divisible by $45$.
    have h_10395_valid : 10000 ≤ 10395 ∧ 10395 < 100000 ∧ (∃ k : Nat, 10395 = 45 * k) ∧ List.Nodup (Nat.digits 10 10395) := by
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · exists 231
      · have h_digits_10395 : Nat.digits 10 10395 = [5, 9, 3, 0, 1] := by norm_num
        rw [h_digits_10395]
        simp [List.Nodup]
    exact h_10395_valid
  · -- Subgoal : Prove that all numbers satisfying the conditions are greater than $10395$.
    intro n h_n
    -- The smallest five-digit natural number is $10000$, and $45 * 222$ is not a five-digit number.
    have h_min_five_digit : 10000 ≤ n := h_n.left
    have h_9990_not_five : 45 * 222 = 9990 ∧ 9990 < 10000 := by
      norm_num
    -- Check $k ∈ [223, 230]$, prove that each $n = 45k$ has repeated digits.
    have h_k_lt_231_repeats : ∀ k : Nat, 223 ≤ k ∧ k ≤ 230 → ¬List.Nodup (Nat.digits 10 (45 * k)) := by
      intros k h_k
      have h_k_bounds : k ∈ Finset.Icc 223 230 := by
        simp [Finset.mem_Icc]
        exact h_k
      -- Check that all $k ∈ [223, 230]$ result in repeated digits.
      fin_cases h_k_bounds
      · have h_digits_10035 : Nat.digits 10 10035 = [5, 3, 0, 0, 1] := by norm_num
        rw [h_digits_10035]
        simp [List.Nodup]
      · have h_digits_10080 : Nat.digits 10 10080 = [0, 8, 0, 0, 1] := by norm_num
        rw [h_digits_10080]
        simp [List.Nodup]
      · have h_digits_10125 : Nat.digits 10 10125 = [5, 2, 1, 0, 1] := by norm_num
        rw [h_digits_10125]
        simp [List.Nodup]
      · have h_digits_10170 : Nat.digits 10 10170 = [0, 7, 1, 0, 1] := by norm_num
        rw [h_digits_10170]
        simp [List.Nodup]
      · have h_digits_10215 : Nat.digits 10 10215 = [5, 1, 2, 0, 1] := by norm_num
        rw [h_digits_10215]
        simp [List.Nodup]
      · have h_digits_10260 : Nat.digits 10 10260 = [0, 6, 2, 0, 1] := by norm_num
        rw [h_digits_10260]
        simp [List.Nodup]
      · have h_digits_10305 : Nat.digits 10 10305 = [5, 0, 3, 0, 1] := by norm_num
        rw [h_digits_10305]
        simp [List.Nodup]
      · have h_digits_10350 : Nat.digits 10 10350 = [0, 5, 3, 0, 1] := by norm_num
        rw [h_digits_10350]
        simp [List.Nodup]
    -- Prove that $n ≥ 10395$.
    have h_n_ge_10395 : n ≥ 10395 := by
      rcases h_n with ⟨h_five_lower, h_five_upper, h_div_45, h_no_repeats⟩
      obtain ⟨k, h_n_eq_45k⟩ := h_div_45
      have h_k_ge_223 : k ≥ 223 := by omega
      have h_k_ge_231 : k ≥ 231 := by
        by_contra h_k_lt_231
        have h_k_le_230 : k ≤ 230 := by nlinarith
        have h_k_in_223_230 : 223 ≤ k ∧ k ≤ 230 := ⟨h_k_ge_223, h_k_le_230⟩
        have h_repeats : ¬List.Nodup (Nat.digits 10 (45 * k)) := h_k_lt_231_repeats k h_k_in_223_230
        rw [← h_n_eq_45k] at h_repeats
        contradiction
      nlinarith
    exact h_n_ge_10395
