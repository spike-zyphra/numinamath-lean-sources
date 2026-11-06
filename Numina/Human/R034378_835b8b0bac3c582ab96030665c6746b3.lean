import Mathlib

/-The number 5.6 may be expressed uniquely (ignoring order) as a product $\underline{a} \cdot \underline{b} \times \underline{c} . \underline{d}$ for digits $a, b, c, d$ all nonzero. Compute $\underline{a} \cdot \underline{b}+\underline{c} \cdot \underline{d}$.-/
theorem number_theory_610639 (a b c d : ℕ) (hpos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (hdig : a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10)
    (hmul : 5.6 = (Nat.ofDigits 10 [a, b] : ℚ) / 10 * ((Nat.ofDigits 10 [c, d] : ℚ) / 10)) :
    (Nat.ofDigits 10 [a, b] : ℚ) / 10 + (Nat.ofDigits 10 [c, d] : ℚ) / 10 = 5.1 := by
-- Simplify the multiplication assumption and the goal by `field_simp`, `norm_num`, `norm_cast`
  field_simp at *; norm_num at *; norm_cast at *
-- Remove `Nat.ofDigits` by `Nat.ofDigits_eq_sum_mapIdx`
  simp [Nat.ofDigits_eq_sum_mapIdx] at *
-- Write down all divisors of $560$ by `decide`
  have div560 : Nat.divisors 560 =
  {1, 2, 4, 5, 7, 8, 10, 14, 16, 20, 28, 35, 40, 56, 70, 80, 112, 140, 280, 560} := by decide
-- Since $a+b*10$ is a divisor of $560$, we can discuss all possible cases and finish the goal with `omega` tactics
  have : a + b * 10 ∈ Nat.divisors 560 := by simp; use c+d*10
  simp [div560] at this; symm at hmul
  apply Nat.eq_div_of_mul_eq_right at hmul
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  any_goals omega
  all_goals simp [h] at hmul; omega