import Mathlib

open Polynomial

/-XIX OM - II - Problem 1

Prove that a polynomial in the variable $ x $ with integer coefficients, whose absolute value for three different integer values of $ x $ equals 1, does not have integer roots.-/
theorem algebra_123604 {p : ℤ[X]} {a b c : ℤ} (abcne : a ≠ b ∧ b ≠ c ∧ c ≠ a)
    (ha : |p.eval a| = 1) (hb : |p.eval b| = 1) (hc : |p.eval c| = 1) :
    ¬ ∃ k, p.IsRoot k := by
-- Assume the contrary that we have an integer root $k$
  push_neg; intro k hk; simp [IsRoot] at hk
-- Apply the `sub_dvd_eval_sub` to get three divisibility assumptions
  have dvd1 := sub_dvd_eval_sub a k p
  have dvd2 := sub_dvd_eval_sub b k p
  have dvd3 := sub_dvd_eval_sub c k p
  simp [hk] at dvd1 dvd2 dvd3
-- Simplify the assumptions and get a contradiction from linear arithmetic
  rw [← dvd_abs] at dvd1 dvd2 dvd3
  rw [ha, ← Int.natAbs_dvd] at dvd1
  norm_cast at dvd1; simp at dvd1
  simp [Int.natAbs_eq_iff] at dvd1
  rw [hb, ← Int.natAbs_dvd] at dvd2
  norm_cast at dvd2; simp at dvd2
  simp [Int.natAbs_eq_iff] at dvd2
  rw [hc, ← Int.natAbs_dvd] at dvd3
  norm_cast at dvd3; simp at dvd3
  simp [Int.natAbs_eq_iff] at dvd3
  omega