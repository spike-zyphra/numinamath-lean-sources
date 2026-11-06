import Mathlib
open Finset Set Nat Real
noncomputable section

/- Find all possible values for the sum of the digits of a square. -/
theorem number_theory_604657 (n : ℕ) :
    (digits 10 (n ^ 2)).sum ≡ 0 [MOD 9] ∨ (digits 10 (n ^ 2)).sum ≡ 1 [MOD 9] ∨
    (digits 10 (n ^ 2)).sum ≡ 4 [MOD 9] ∨ (digits 10 (n ^ 2)).sum ≡ 7 [MOD 9] := by
  -- Use Nat.nine_dvd_iff: $.(digits 10 (n ^ 2)).sum ≡ n ^ 2 [MOD 9]$
  have h_digit_sum : n ^ 2 ≡ (digits 10 (n ^ 2)).sum [MOD 9] := by
    exact Nat.modEq_nine_digits_sum (n ^ 2)
  -- Decompose $n$ modulo $9$: $n = 9k + r$, $r ∈ {0, 1, ..., 8}$.
  let r := n % 9
  have h_mod : n ≡ r [MOD 9] := by
    have : n % 9 = r % 9 := by
      unfold r
      rw [Nat.mod_eq_of_lt (Nat.mod_lt n (by exact Nat.zero_lt_succ 8))]
    show n % 9 = r % 9
    exact this
  -- Prove $n ^ 2 ≡ r ^ 2 [MOD 9]$.
  have h_square : n ^ 2 ≡ r ^ 2 [MOD 9] := by
    exact Nat.ModEq.pow 2 h_mod
  -- From h_digit_sum and h_square, $(digits 10 (n ^ 2)).sum ≡ r ^ 2 [MOD 9]$.
  have h_digit_square : (digits 10 (n ^ 2)).sum ≡ r ^ 2 [MOD 9] := by
    apply Nat.ModEq.trans h_digit_sum.symm h_square
  -- Enumerate $r$ from $0$ to $8$, compute $r ^ 2$ mod $9$.
  have h_r_bound : r < 9 := Nat.mod_lt n (by norm_num)
  match r with
  | 0 =>
    have h_r : 0 ^ 2 = 0 := by norm_num
    left
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 1 =>
    have h_r : 1 ^ 2 = 1 := by norm_num
    right; left
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 2 =>
    have h_r : 2 ^ 2 = 4 := by norm_num
    right; right; left
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 3 =>
    have h_r : 3 ^ 2 = 9 := by norm_num
    left
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 4 =>
    have h_r : 4 ^ 2 = 16 := by norm_num
    right; right; right
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 5 =>
    have h_r : 5 ^ 2 = 25 := by norm_num
    right; right; right
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 6 =>
    have h_r : 6 ^ 2 = 36 := by norm_num
    left
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 7 =>
    have h_r : 7 ^ 2 = 49 := by norm_num
    right; right; left
    simp [h_r] at h_digit_square
    exact h_digit_square
  | 8 =>
    have h_r : 8 ^ 2 = 64 := by norm_num
    right; left
    simp [h_r] at h_digit_square
    exact h_digit_square