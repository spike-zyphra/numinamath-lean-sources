import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_288791 :
    {k : ℝ | ∀ a b c d : ℝ, a ≥ -1 → b ≥ -1 → c ≥ -1 → d ≥ -1 → a^3 + b^3 + c^3 + d^3 + 1 ≥ k * (a + b + c + d)} = {3 / 4} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if k satisfies the inequality, then k = 3/4
    intro h
    have h1 := h (-1) (-1) (-1) (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h1' : k ≥ 3 / 4 := by 
      nlinarith
    have h2 := h (1 / 2) (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h2' : k ≤ 3 / 4 := by
      nlinarith
    linarith [h1', h2']
  · -- Second direction: k = 3/4 satisfies the inequality
    intro hk
    rw [hk]
    intro a b c d ha hb hc hd
    have h1 : a^3 - 3 / 4 * a ≥ -1 / 4 := by
      nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1), sq_nonneg (a - (-1)), sq_nonneg (a - 1 / 2), sq_nonneg ((a * 2) + 1), sq_nonneg ((a * 2) - 1)]
    have h2 : b^3 - 3 / 4 * b ≥ -1 / 4 := by
      nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (b + 1), sq_nonneg (b - (-1)), sq_nonneg (b - 1 / 2), sq_nonneg ((b * 2) + 1), sq_nonneg ((b * 2) - 1)]
    have h3 : c^3 - 3 / 4 * c ≥ -1 / 4 := by
      nlinarith [sq_nonneg (c + 1), sq_nonneg (c - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (c + 1), sq_nonneg (c - (-1)), sq_nonneg (c - 1 / 2), sq_nonneg ((c * 2) + 1), sq_nonneg ((c * 2) - 1)]
    have h4 : d^3 - 3 / 4 * d ≥ -1 / 4 := by
      nlinarith [sq_nonneg (d + 1), sq_nonneg (d - 1 / 2), sq_nonneg (d - 1 / 2), sq_nonneg (d + 1), sq_nonneg (d - (-1)), sq_nonneg (d - 1 / 2), sq_nonneg ((d * 2) + 1), sq_nonneg ((d * 2) - 1)]
    linarith [h1, h2, h3, h4]