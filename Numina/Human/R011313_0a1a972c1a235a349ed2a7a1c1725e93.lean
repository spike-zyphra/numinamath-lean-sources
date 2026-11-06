import Mathlib

/- Find the sum of the absolute values of the roots of $x^{4}-4 x^{3}-4 x^{2}+16 x-8=0$. -/
theorem algebra_611312 {s : Set ℝ} (hs : s = {x : ℝ | x ^ 4 - 4 * x ^ 3 - 4 * x ^ 2 + 16 * x - 8 = 0}) :
    ∑ᶠ x ∈ s, |x| = 2 + 2 * √2 + 2 * √3 := by
  -- Suffices to show solution of $x^{4}-4 x^{3}-4 x^{2}+16 x-8=0$ are
  -- $1 + √2 + √3, 1 + √2 - √3, 1 - √2 + √3, 1 - √2 - √3$.
  suffices s = {1 + √2 + √3, 1 + √2 - √3, 1 - √2 + √3, 1 - √2 - √3} by
    -- Transform `Set` to `Finset`.
    have : s = ({1 + √2 + √3, 1 + √2 - √3, 1 - √2 + √3, 1 - √2 - √3} : Finset ℝ) := by simp [this]
    -- Transform `finsum` to `Finset.sum`.
    rw [this, finsum_mem_coe_finset]
    -- Expand `Finset.sum`.
    repeat rw [Finset.sum_insert]
    -- Need `0 < 1 + √2 - √3` to remove `abs`.
    have : 0 < 1 + √2 - √3 := by
      suffices √3 < 1 + √2 by linarith
      rw [← pow_lt_pow_iff_left₀ (n := 2) (by positivity) (by positivity) (by norm_num),
        Real.sq_sqrt (by norm_num), add_sq, Real.sq_sqrt (by norm_num)]
      suffices 0 < 2 * √2 by linarith
      positivity
    -- Need `0 < 1 - √2 + √3` to remove `abs`.
    have : 0 < 1 - √2 + √3 := by
      suffices √2 < 1 + √3 by linarith
      rw [← pow_lt_pow_iff_left₀ (n := 2) (by positivity) (by positivity) (by norm_num),
        Real.sq_sqrt (by norm_num), add_sq, Real.sq_sqrt (by norm_num)]
      suffices -2 < 2 * √3 by linarith
      exact lt_trans (by norm_num : -2 < (0 : ℝ)) (by positivity)
    -- Need `1 - √2 - √3 < 0` to remove `abs`.
    have : 1 - √2 - √3 < 0 := by
      suffices 1 < √2 + √3 by linarith
      trans √2
      . rw [← pow_lt_pow_iff_left₀ (n := 2) (by positivity) (by positivity) (by norm_num),
          Real.sq_sqrt (by norm_num)]
        norm_num
      . simp
    -- Remove all `abs`.
    rw [Finset.sum_singleton, abs_of_pos (by positivity), abs_of_pos ‹_›, abs_of_pos ‹_›,
      abs_of_neg ‹_›]
    -- `ring` can solve this identity.
    ring
    . -- Show `1 - √2 + √3 ∉ {1 - √2 - √3}`.
      intro h
      rw [Finset.mem_singleton] at h
      have : 2 * √3 = 0 := by linear_combination h
      simp at this
    . -- Show ` 1 + √2 - √3 ∉ {1 - √2 + √3, 1 - √2 - √3}`.
      intro h
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      . have : 2 * √2 = 2 * √3 := by linear_combination h
        simp at this
      . have : 2 * √2 = 0 := by linear_combination h
        simp at this
    . -- Show `1 + √2 + √3 ∉ {1 + √2 - √3, 1 - √2 + √3, 1 - √2 - √3}`.
      intro h
      simp at h
      rcases h with h | h | h
      . have : 2 * √3 = 0 := by linear_combination h
        simp at this
      . have : 2 * √2 = 0 := by linear_combination h
        simp at this
      . have : 2 * (√2 + √3) = 0 := by linear_combination h
        linarith [show 0 < 2 * (√2 + √3) by positivity]
  ext x
  -- It's clear that `x ∈ {a, b, c, d}` if and only if `(x - a) * (x - b) * (x - c) * (x - d) = 0`.
  have {a b c d : ℝ} (x : ℝ) : x ∈ ({a, b, c, d} : Set ℝ) ↔
      (x - a) * (x - b) * (x - c) * (x - d) = 0 := by
    simp [sub_eq_zero]; tauto
  rw [this, hs, Set.mem_setOf]
  apply Eq.congr_left
  -- We can show `x ^ 4 - 4 * x ^ 3 - 4 * x ^ 2 + 16 * x - 8` equals to
  -- `(x - (1 + √2 + √3)) * (x - (1 + √2 - √3)) * (x - (1 - √2 + √3)) * (x - (1 - √2 - √3))`
  -- by simple calculation.
  calc
    _ = (x ^ 2 - 2 * x) ^ 2 - 8 * (x - 1) ^ 2 := by ring
    _ = (x ^ 2 - 2 * x) ^ 2 - (2 * √2 * x - 2 * √2) ^ 2 := by
      congr 1; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
    _ = (x ^ 2 - (2 + 2 * √2) * x + 2 * √2) * (x ^ 2 - (2 - 2 * √2) * x - 2 * √2) := by
      rw [sq_sub_sq, mul_comm]; congr 1 <;> ring
  rw [mul_assoc]
  congr 1
  all_goals
    ring_nf
    repeat rw [Real.sq_sqrt (by norm_num)]
    ring
