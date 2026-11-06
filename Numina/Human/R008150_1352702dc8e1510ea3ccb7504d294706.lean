import Mathlib

/- Using Fermat's little theorem, find the last digit of the base 7 expansion of \(3^{100}\).-/
theorem number_theory_4784 : 3^100 ≡ 4 [ZMOD 7] := by
  set n : ℕ := 7 with hn
  have prime_seven : Nat.Prime n := by norm_num
  -- need coprime condition for using Fermat's Little Theorem
  have three_co_seven : IsCoprime (3 : ℤ) n := by
    rw [Int.isCoprime_iff_gcd_eq_one, hn]
    decide
  rw [show 100 = (n-1) * 16 + 4 by norm_num]
  rw [pow_add, pow_mul]
  nth_rw 2 [← one_mul 4]
  -- verify 3^4=4 mod 7 by computation
  refine Int.ModEq.mul ?_ (by decide)
  nth_rw 2 [← one_pow 16]
  -- suffices to show 3^(n-1)=1 mod 7
  -- which is exactly `Int.ModEq.pow_card_sub_one_eq_one` in Mathlib
  apply Int.ModEq.pow
  exact Int.ModEq.pow_card_sub_one_eq_one prime_seven three_co_seven
