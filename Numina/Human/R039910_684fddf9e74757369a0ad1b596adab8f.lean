import Mathlib

open Real Set
open scoped BigOperators

/-Suppose $x \in [-5,-3]$ and $y \in [2,4]$. What is the smallest possible value of $\frac{x+y}{x-y}$?-/
theorem algebra_22447 :
  IsLeast {z : ℝ | ∃ x y, x ∈ Icc (-5) (-3) ∧ y ∈ Icc 2 4 ∧ z = (x + y) / (x - y)} (-1 / 7) := by
  unfold IsLeast
  constructor
  -- Show that -1/7 is an element of the set
  · use -3
    use 4
    simp
    repeat use (by norm_num)
  -- Show that -1/7 is a lower bound of the set
  · apply mem_lowerBounds.mpr
    intro t
    simp
    intro x hx₀ hx₁ y hy₀ hy₁ ht
    -- Transform the expression to a more manageable form, adding 1
    have ht' : t = (-2 * x) / (y - x) - 1 := by
      rw [ht, ←sub_eq_zero, ←sub_add, neg_mul, ←(neg_sub x y)]
      rw [div_neg, neg_div, neg_neg, ←sub_div]
      rw [show x + y - 2 * x = -(x - y) by linarith, neg_div, div_self]
      repeat linarith
    -- Since y - x is in the denominator, and y can be as large as 4, we aim to minimize the fraction by setting y to 4
    have ine₁ : (-2 * x) / (4 - x) ≤ (-2 * x) / (y - x) := by
      refine div_le_div_of_nonneg_left ?_ ?_ ?_
      repeat linarith
    -- Substituting y = 4, we now try to minimize -2x/(4-x) - 1. We rewrite it as 1-8/(4-x)
    have ht'' : 1 - 8 / (4 - x) ≤ t := by
      rw [ht']
      have : 2 - 8 / (4 - x) ≤ -2 * x / (y - x) := by
        apply le_trans ?_ ine₁
        apply le_of_eq
        rw [←sub_eq_zero, neg_mul, neg_div, sub_neg_eq_add]
        rw [sub_add, ←sub_div, show (8 : ℝ) = 2 * 4 by norm_num]
        rw [←mul_sub, ←mul_div, div_self]
        repeat linarith
      linarith
    -- To minimize 1 - 8 / (4 - x), we maximize 8 / (4 - x), which means we need to minimize 4-x, which occurs when x = -3
    have ine₂ : -1/7 ≤ 1 - 8 / (4 - x) := by
      have : 8 / (4 - x) ≤ 8/7 := by
        refine div_le_div_of_nonneg_left ?_ ?_ ?_
        repeat linarith
      linarith
    -- Putting it together, -1/7 <= 1 - 8 / (4 - x) <= t
    linarith
