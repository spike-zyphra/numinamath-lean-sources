import Mathlib

open Nat

/- Let $A$ be the sum of the digits of the number $4444^{4444}$, and $B$ be the sum of the digits of the number $A$. Find the sum of the digits of the number $B$.

# -/
theorem number_theory_229899 :
    (digits 10 (digits 10 (digits 10 (4444 ^ 4444)).sum).sum).sum = 7 := by
  -- We have the sum of digits of n is congruent to n mod 9
  -- So the result is congruent to 4444 ^ 4444 mod 9
  -- 4444 ^ 4444 ≡ 7 ^ 4444 = (7 ^ 3) ^ 1481 * 7 ≡ 1 ^ 1481 * 7 ≡ 7 [MOD 9]
  have H : (digits 10 (digits 10 (digits 10 (4444 ^ 4444)).sum).sum).sum ≡ 7 [MOD 9] := by
    calc (digits 10 (digits 10 (digits 10 (4444 ^ 4444)).sum).sum).sum
      _ ≡ (digits 10 (digits 10 (4444 ^ 4444)).sum).sum [MOD 9] := (modEq_nine_digits_sum _).symm
      _ ≡ (digits 10 (4444 ^ 4444)).sum [MOD 9] := (modEq_nine_digits_sum _).symm
      _ ≡ 4444 ^ 4444 [MOD 9] := (modEq_nine_digits_sum _).symm
      _ ≡ 7 ^ 4444 [MOD 9] := ModEq.pow _ (by decide)
      _ = (7 ^ 3) ^ 1481 * 7 ^ 1 := by
        rewrite [← pow_mul, ← pow_add]
        congrm 7 ^ ?_
        simp
      _ ≡ 1 ^ 1481 * 7 ^ 1 [MOD 9] := ModEq.mul_right _ (ModEq.pow _ (by decide))
      _ = 7 := by rw [one_pow, one_mul, pow_one]
  -- We give a bound on the sum of the digits of a number
  have lem {x n : ℕ} (hx : x < 10 ^ n) : (digits 10 x).sum ≤ 9 * n := by
    by_cases hx' : x = 0
    . simp [hx']
    calc (digits 10 x).sum
      -- Since every digit is ≤ 9, the sum is ≤ 9 * the number of digits
      _ ≤ (digits 10 x).length * 9 := List.sum_le_card_nsmul _ _ fun d hd => le_of_lt_succ (Nat.digits_lt_base (by simp) hd)
      _ = 9 * (log 10 x + 1) := by rw [← Nat.digits_len _ _ (by simp) hx', mul_comm]
      _ ≤ 9 * n := by gcongr; rw [succ_le]; exact log_lt_of_lt_pow hx' hx
  -- So the sum of the digits of 4444 ^ 4444 is ≤ 180000
  have h₁ : (digits 10 (4444 ^ 4444)).sum ≤ 180000 := by
    apply lem (n := 20000)
    calc 4444 ^ 4444
      _ < (10 ^ 4) ^ 4444 := by rw [Nat.pow_lt_pow_iff_left (by simp)]; simp
      _ = 10 ^ (4 * 4444) := by rw [pow_mul]
      _ < 10 ^ 20000 := by apply Nat.pow_lt_pow_of_lt <;> simp
  -- So the sum of the digits of the sum of the digits of 4444 ^ 4444 is ≤ 54
  have h₂ : (digits 10 (digits 10 (4444 ^ 4444)).sum).sum ≤ 54 := by
    apply lem (n := 6)
    calc _
      _ ≤ 180000 := h₁
      _ < 10 ^ 6 := by simp
  -- Any x ≤ 54 such that x ≡ 7 [MOD 9] has digits summing to 7
  generalize (digits 10 (digits 10 (4444 ^ 4444)).sum).sum = x at h₂ H
  clear lem h₁
  revert h₂ H x
  native_decide
