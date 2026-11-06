import Mathlib


open Nat


lemma nat_le_iff_lt_add_one : x ≤ y ↔ x < y + 1 := by
  omega



lemma nat_div_le_iff_le_mul (h : 0 < k) : x / k ≤ y ↔ x ≤ y * k + k - 1 := by
  rw [nat_le_iff_lt_add_one, Nat.div_lt_iff_lt_mul h, Nat.add_one_mul]
  omega


lemma nat_div_eq_iff (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x ≤ y * k + k - 1 := by
  rw [Nat.eq_iff_le_and_ge, and_comm, le_div_iff_mul_le h, nat_div_le_iff_le_mul h]



theorem number_theory_642074 (n : ℕ) (hn : n > 0) :
  (Nat.digits 10 (2^(n + 54) * 5^(n + 3) / 4^27)).length = n + 3 := by 
  have h2 : ∀ m : ℕ, 2 ^ (m + 54) * 5 ^ (m + 3) / 4 ^ 27 = 125 * 10 ^ m := by
    intro m
    have h3 : 2 ^ (m + 54) * 5 ^ (m + 3) = 2 ^ m * 5 ^ m * 2 ^ 54 * 5 ^ 3 := by
      calc
        2 ^ (m + 54) * 5 ^ (m + 3) = (2 ^ m * 2 ^ 54) * (5 ^ m * 5 ^ 3) := by
          ring_nf
        _ = 2 ^ m * 5 ^ m * 2 ^ 54 * 5 ^ 3 := by
          ring_nf
    have h4 : 4 ^ 27 = 2 ^ 54 := by
      calc
        4 ^ 27 = (2 ^ 2) ^ 27 := by
          norm_num
        _ = 2 ^ (2 * 27) := by
          rw [← pow_mul]
        _ = 2 ^ 54 := by
          norm_num
    rw [h3, h4]
    have h5 : 2 ^ 54 > 0 := by positivity
    have h6 : 5 ^ 3 > 0 := by positivity
    have h7 : 2 ^ m * 5 ^ m > 0 := by positivity
    refine (nat_div_eq_iff ?_).mpr ?_
    · positivity
    have aux : 2 ^ m * 5 ^ m * 2 ^ 54 * 5 ^ 3 = 125 * 10 ^ m * 2 ^ 54 := by 
      rw [show 10 = 2 * 5 by norm_num, mul_pow]
      ring_nf
    constructor
    · rw [aux]
    · 
      rw [aux]
      have aux2 : 2 ^ 54 - 1 ≥ 0 := by 
        nlinarith
      have ineq : 125 * 10 ^ m * 2 ^ 54 + 2 ^ 54 ≥ 1 := by 
        nlinarith
      have aux3 : 125 * 10 ^ m * 2 ^ 54 + 2 ^ 54 - 1 = 125 * 10 ^ m * 2 ^ 54 + (2 ^ 54 - 1) := by 
        omega
      rw [aux3]
      linarith
  rw [Nat.digits_len]
  rw [h2 n]
  have h6 : 125 * 10 ^ n > 0 := by positivity
  · have aux2 : log 10 (125 * 10 ^ n) = n + 2 := by 
      refine (Nat.log_eq_iff ?_).mpr ?_
      constructor
      · linarith
      constructor
      · rw [pow_add]
        simp
        linarith
      · 
        rw [pow_add, pow_add]
        simp
        linarith
    omega
  · linarith
  · rw [h2]
    have pos : 125 * 10 ^ n > 0 := by 
      positivity
    linarith
