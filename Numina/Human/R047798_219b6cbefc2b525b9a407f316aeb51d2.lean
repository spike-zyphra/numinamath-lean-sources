import Mathlib
set_option maxRecDepth 5000

/-Find the smallest positive integer $b$ for which $x^2+bx+2008$ factors into a product of two binomials, each having integer coefficients.-/
theorem algebra_14852 : IsLeast {m : ℤ | 0 < m ∧ (∃ r s : ℤ, ∀ x : ℝ, x ^ 2 +
    m * x + 2008 = (x + r) * (x + s))} 259 := by
-- Rewrite goals and introduce assumptions
  simp [IsLeast, lowerBounds]; constructor
  · use 251; use 8; intro; ring
  intro m hm r s h
-- Find the relation between $m$, $r$ and $t$
  have hmul := h 0; simp at hmul
  have hadd := h 1; ring_nf at hadd
  rw [← hmul] at hadd; ring_nf at hadd
  rw [add_assoc] at hadd; simp at hadd
  norm_cast at hadd hmul
-- Prove that $r$ and $s$ is positive
  have rspos : 0 < r ∧ 0 < s := by
    have : 0 < r * s := by linarith
    rw [mul_pos_iff] at this; cases this
    assumption; linarith
-- Rewrite the final goal
  rw [hadd]
-- Prove that the absolute value of $r$ is a divisor of $2008$
  have rdiv: r.natAbs ∈ Nat.divisors 2008 := by
    rw [Nat.mem_divisors]; simp; use s.natAbs
    rw [← Int.natAbs_mul, ← hmul]; norm_num
  rw [← Int.ediv_eq_iff_eq_mul_right] at hmul
-- Write out all possible divisors of 2008
  have : Nat.divisors 2008 = {1, 2, 4, 8, 251, 502, 1004, 2008} := by decide
  simp [this] at rdiv; zify at rdiv
  repeat rw [abs_eq_self.mpr] at rdiv
-- Check all possible values of $r$ and finish the final goal
  rcases rdiv with hr|hr|hr|hr|hr|hr|hr|hr
  any_goals simp [hr] at hmul; simp [hr, ← hmul]
  any_goals linarith only [rspos.left]
  use s
