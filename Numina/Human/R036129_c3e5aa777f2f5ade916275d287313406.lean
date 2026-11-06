import Mathlib

open Finset

/- 1. Variant 1.

When multiplying two two-digit numbers, a four-digit number $A$ is obtained, where the first digit matches the second, and the second-to-last digit matches the last. Find the smallest $A$, given that $A$ is divisible by 51. -/
theorem number_theory_290095 :
    IsLeast {A | (∃ a b, a ∈ Icc 10 99 ∧ b ∈ Icc 10 99 ∧ A = a * b) ∧ A ∈ Icc 1000 9999
      ∧ (∃ x y, Nat.digits 10 A = [x, x, y, y]) ∧ 51 ∣ A} 1122 := by
  simp only [IsLeast, mem_Icc, Nat.reduceLeDiff, Set.mem_setOf_eq, Nat.ofNat_pos,
    Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, zero_lt_one, Nat.one_mod,
    Nat.digits_zero, List.cons.injEq, and_true, and_self, and_self_left, exists_eq', true_and,
    lowerBounds, and_imp, forall_exists_index]
  -- it is easy to show that 1122 satisfies all requirements (1122 = 22 * 51)
  refine ⟨⟨⟨22, 51, by norm_num⟩, by norm_num⟩, ?_⟩
  intro B a b ha1 ha2 hb1 hb2 hBab hB1 hB2 x y hBxy h51
  -- B = 1000 * y + 100 * y + 10 * x + x = 11 * (100 * y + x)
  have hB : B = 11 * (100 * y + x) := by
    rw [←Nat.ofDigits_digits 10 B, hBxy]
    simp only [Nat.ofDigits, Nat.cast_id, mul_zero, add_zero]
    ring
  -- 51 divides B = 11 * (100 * y + x), so 51 divides 100 * y + x (since 11 and 51 are coprime)
  have ⟨k, hk⟩ : ∃ k, 100 * y + x = 51 * k := by
    exact (show Nat.Coprime 51 11 by norm_num).dvd_of_dvd_mul_left (hB ▸ h51)
  -- if k >= 2 then B >= 1122
  -- the cases k = 0 or k = 1 are impossible because y ≥ 1 (it follows from B ≥ 1000)
  omega