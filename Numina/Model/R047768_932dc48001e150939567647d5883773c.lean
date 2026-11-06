import Mathlib

def isAlternating (n : ℕ) : Prop :=
  (Nat.digits 10 n).length = 5 ∧
  (Nat.digits 10 n).toFinset.card = 2 ∧
  ∃ a b, a ≠ b ∧ (Nat.digits 10 n) = [a, b, a, b, a]

theorem number_theory_255688 :
    {n | 15 ∣ n ∧ isAlternating n}.encard = 4 := by
  have h1 : {n | 15 ∣ n ∧ isAlternating n} = {50505, 53535, 56565, 59595} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is divisible by 15 and is alternating.
      intro h
      rcases h with ⟨h15, ⟨h3, h4, ⟨a, b, hab, hp⟩⟩⟩
      have h2 : n % 15 = 0 := by
        omega
      have h5 : (Nat.digits 10 n).length = 5 := h3
      have h6 : (Nat.digits 10 n).toFinset.card = 2 := h4
      have h7 : (Nat.digits 10 n) = [a, b, a, b, a] := hp
      have h8 : n = a * 10000 + b * 1000 + a * 100 + b * 10 + a := by
        rw [← Nat.ofDigits_digits 10 n]
        rw [h7]
        simp [Nat.ofDigits, mul_add, mul_assoc]
        all_goals
          ring
      have ha0 : a ≤ 9 := by
        have h9 : a ∈ Nat.digits 10 n := by
          rw [hp]
          simp
        have h10 : a < 10 := by
          exact Nat.digits_lt_base (by norm_num) h9
        omega
      have hb0 : b ≤ 9 := by
        have h9 : b ∈ Nat.digits 10 n := by
          rw [hp]
          simp
        have h10 : b < 10 := by
          exact Nat.digits_lt_base (by norm_num) h9
        omega
      interval_cases a <;> interval_cases b
      <;> norm_num [h8, hp] at *
      <;> tauto
    · -- Assume n is in the set.
      rintro (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · constructor
          · native_decide
          · constructor
            · native_decide
            · use 5, 0
              all_goals native_decide
      · constructor
        · norm_num
        · constructor
          · native_decide
          · constructor
            · native_decide
            · use 5, 3
              all_goals native_decide
      · constructor
        · norm_num
        · constructor
          · native_decide
          · constructor
            · native_decide
            · use 5, 6
              all_goals native_decide
      · constructor
        · norm_num
        · constructor
          · native_decide
          · constructor
            · native_decide
            · use 5, 9
              all_goals native_decide
  rw [h1]
  rw [Set.encard]
  simp