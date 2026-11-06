import Mathlib

/- 1.15 $\star \star$ For what minimum value of the natural number $n$ does the equation

$$

\left[\frac{10^{n}}{x}\right]=1989

$$

have an integer solution? -/
theorem number_theory_99259 :
    IsLeast {n | ∃ x : ℤ, ⌊(10^n / x : ℝ)⌋ = 1989} 7 := by
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index]
  constructor
  -- Show that there exists an integer x for n = 7.
  -- Take x = 5026 and compute that ⌊10 ^ 7 / 5026⌋ = 1989.
  · use 5026
    norm_num
  -- Suppose that ⌊10 ^ n / x⌋ = 1989 and show that 7 ≤ n.
  intro n x h
  -- ⌊10 ^ n / x⌋ = 1989 implies that 1989 ≤ 10 ^ n / x.
  have ineq1 : 1989 ≤ 10 ^ n / (x : ℝ) := by
    rw [show (1989 : ℝ) = (1989 : ℤ) by simp, ← Int.le_floor, ← h]
  -- ⌊10 ^ n / x⌋ = 1989 implies that 10 ^ n / x < 1990.
  have ineq2 : 10 ^ n / (x : ℝ) < 1990 := by
    rw [show (1990 : ℝ) = (1990 : ℤ) by simp, ← Int.floor_lt, h]
    norm_num
  -- Prove that 0 < x.
  have hx : 0 < (x : ℝ) := by
    -- Suppose that 0 ≤ x and show that 10 ^ n / x < 1989.
    contrapose! ineq1
    -- We have 10 ^ n / x ≤ 0 < 1989.
    apply lt_of_le_of_lt _ (show 0 < (1989 : ℝ) by norm_num)
    apply div_nonpos_of_nonneg_of_nonpos _ ineq1
    positivity
  -- Rewrite inequalities as follows:
  -- 1989 * x ≤ 10 ^ n and 10 ^ n < 1990 * x.
  rw [le_div_iff₀ hx] at ineq1
  rw [div_lt_iff₀ hx] at ineq2
  norm_cast at hx
  -- All inequalities can be considered as inequalities in ℕ because 0 < x.
  lift x to ℕ using le_of_lt hx
  norm_cast at ineq1 ineq2 hx
  -- Consider the following cases: n ≤ 3, n = 4, n = 5, n = 6, or 7 ≤ n.
  rcases show n <= 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega with hn | hn | hn | hn | hn
  -- If n ≤ 3 then the inequality 1989 * x ≤ 10 ^ n does not hold.
  · contrapose! ineq1
    apply lt_of_le_of_lt _ (show 10 ^ 3 < 1989 * x by omega)
    exact Nat.pow_le_pow_right (by norm_num) hn
  -- If n = 4 then the interval [10^4 / 1989, 10^4 / 1990) does not contain integers.
  · subst n
    omega
  -- If n = 5 then the interval [10^5 / 1989, 10^5 / 1990) does not contain integers.
  · subst n
    omega
  -- If n = 6 then the interval [10^6 / 1989, 10^6 / 1990) does not contain integers.
  · subst n
    omega
  -- We conclude that 7 ≤ n.
  · exact hn