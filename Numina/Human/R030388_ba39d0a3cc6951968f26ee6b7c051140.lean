import Mathlib

/-The sum of 18 consecutive positive integers is a perfect square.  What is the smallest possible value of this sum?-/
theorem algebra_16461 :
IsLeast {n | (∃ k, n = ∑ i ∈ Finset.range 18, (k + i)) ∧ ∃ m, m ^ 2 = n} 225 := by
-- Introduce assumptions and rewrite the goal
  rw [IsLeast, lowerBounds]; simp; constructor
-- Check that $225$ is a sum of 18 consecutive positive integers and also a perfect square
  · constructor; use 4; norm_num
    use 15; norm_num
-- Prove that any number satisfies the assumption has to be greater or equal to $225$
  intro a x h;
  have : ∑ i ∈ Finset.range 18, (a + i) = 9 * (2 * a + 17) := by
    rw [Finset.sum_add_distrib, Finset.sum_const]
    simp; rw [Finset.sum_range_id]; ring
-- Prove by contradiction, we first solve for a range on $a$
  rw [this]; by_contra h'; push_neg at h'
  rw [show 225=9*25 by norm_num, Nat.mul_lt_mul_left] at h'
  rw [show 25=8+17 by norm_num, Nat.add_lt_add_iff_right] at h'
  rw [show 8=2*4 by norm_num, Nat.mul_lt_mul_left] at h'
-- Check all possible values of $a$ and finish the final goals
  interval_cases a
  · rw [this] at h; norm_num at h
    have : x < 13 := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    have : 12 < x := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    linarith
  · simp_all
    have : x < 14 := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    have : 13 < x := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    linarith
  · simp_all
    have : x < 14 := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    have : 13 < x := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    linarith
  · simp_all
    have : x < 15 := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    have : 14 < x := by rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by norm_num)]; linarith
    linarith
  any_goals norm_num