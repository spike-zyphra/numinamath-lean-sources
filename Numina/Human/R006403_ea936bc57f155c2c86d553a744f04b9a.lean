import Mathlib

/-
Let X be a positive integer. A four–digit number n can be written as n = 1000·a + 100·b + 10·c + d, where a, b, c, d are its digits with a ≠ 0.
Define reverse(n) = 1000·d + 100·c + 10·b + a, assuming d ≠ 0 so that reverse(n) is also a four–digit number.  We want to find all n satisfying X · n = reverse(n).
Prove an existence statement showing that when X = 9, there indeed exist digits a,b,c,d (namely 1,0,8,9) making n = 1089 a solution.
-/

theorem exists_digits_for_1089
  (X : Nat)
  (hX : X = 9)
  (rev : Nat → Nat)
  (hrev : ∀ (a b c d : Nat), rev (1000 * a + 100 * b + 10 * c + d) = 1000 * d + 100 * c + 10 * b + a) :
  ∃ (a b c d : Nat),
    a ≠ 0 ∧ d ≠ 0 ∧
    1089 = 1000 * a + 100 * b + 10 * c + d ∧
    X * (1000 * a + 100 * b + 10 * c + d) = rev (1000 * a + 100 * b + 10 * c + d) := by
  -- We propose a = 1, b = 0, c = 8, d = 9.
  use 1, 0, 8, 9

  constructor
  ·
    simp only [ne_eq,
      one_ne_zero,
      not_false_eq_true]

  ·
    simp only [ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      mul_one,
      mul_zero,
      add_zero,
      Nat.reduceMul,
      Nat.reduceAdd,
      true_and]
    rw [hX]
    rw [hrev 1 0 8 9]
