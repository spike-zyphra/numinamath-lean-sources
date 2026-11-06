import Mathlib

open Finset Real Nat

/- Call a number overweight if it has at least three positive integer divisors (including 1 and the number),
and call a number obese if it has at least four positive integer divisors (including 1 and the number).
How many positive integers between 1 and 200 are overweight, but not obese?-/

theorem number_theory_608438: {n: ℕ | (1 ≤ n) ∧ (n ≤ 200) ∧ (n.divisors.card ≥ 3) ∧ (n.divisors.card < 4)}.encard = 6 := by

  --To solve this problem, we use a smart way to enumurate all possible values of n--
  have enum: ∀ n: ℕ, (1 ≤ n) ∧ (n ≤ 200) ∧ (n ≠ 4) ∧ (n ≠ 9) ∧ (n ≠ 25) ∧ (n ≠ 49) ∧ (n ≠ 121) ∧ (n ≠ 169) → #n.divisors ≠ 3:= by
    intro n
    intro h
    have hn: (n ∈ Icc 1 3) ∨ (n ∈ Icc 5 8) ∨ (n ∈ Icc 10 24) ∨ (n ∈ Icc 26 48) ∨ (n ∈ Icc 50 120) ∨ (n ∈ Icc 122 168) ∨ (n ∈ Icc 170 200) := by
      simp
      omega
    rcases hn with hn | hn | hn | hn | hn | hn | hn
    . fin_cases hn
      all_goals decide
    . fin_cases hn
      all_goals decide
    . fin_cases hn
      all_goals decide
    . fin_cases hn
      all_goals decide
    . let m:= n - 50
      have nm: n = m + 50 := by
        simp [m]
        rw [Nat.sub_add_cancel]
        simp at hn
        omega
      simp [nm]
      have hm: m ∈ Icc 0 70 := by
        simp
        simp at hn
        omega
      clear * - hm
      clear_value m
      fin_cases hm
      all_goals decide
    . let m:= n - 122
      have nm: n = m + 122 := by
        simp [m]
        rw [Nat.sub_add_cancel]
        simp at hn
        omega
      simp [nm]
      have hm: m ∈ Icc 0 46 := by
        simp
        simp at hn
        omega
      clear * - hm
      clear_value m
      fin_cases hm
      all_goals decide
    . let m:= n - 170
      have nm: n = m + 170 := by
        simp [m]
        rw [Nat.sub_add_cancel]
        simp at hn
        omega
      simp [nm]
      have hm: m ∈ Icc 0 30 := by
        simp
        simp at hn
        omega
      clear * - hm
      clear_value m
      fin_cases hm
      all_goals decide

  -- Then we list all possible values of n --
  have set_eq: {n: ℕ | (1 ≤ n) ∧ (n ≤ 200) ∧ (n.divisors.card ≥ 3) ∧ (n.divisors.card < 4)} = {4, 9, 25, 49, 121, 169} := by
    ext n
    constructor

    -- the forward direction --
    . intro hn
      simp at hn
      rcases hn with ⟨b1, b2, h⟩
      replace h: n.divisors.card = 3 := by
        omega
      by_contra! no
      specialize enum n
      simp at no
      simp [no,b1,b2] at enum
      tauto

    -- the backward direction --
    . intro hn
      simp at hn
      simp
      rcases hn with hn | hn | hn | hn | hn | hn
      . rw [hn]
        simp
        have d4: #(divisors 4) = 3 := by
          decide
        simp [d4]
      . rw [hn]
        simp
        have d9: #(divisors 9) = 3 := by
          decide
        simp [d9]
      . rw [hn]
        simp
        have d25: #(divisors 25) = 3 := by
          decide
        simp [d25]
      . rw [hn]
        simp
        have d49: #(divisors 49) = 3 := by
          decide
        simp [d49]
      . rw [hn]
        simp
        have d121: #(divisors 121) = 3 := by
          decide
        simp [d121]
      . rw [hn]
        simp
        have d169: #(divisors 169) = 3 := by
          decide
        simp [d169]

  -- Finally, we calculate the cardinality of the set --
  simp [set_eq,Set.encard]