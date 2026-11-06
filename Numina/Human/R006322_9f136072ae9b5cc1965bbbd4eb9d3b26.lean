import Mathlib
/- Let $M$ be a positive integer. Show that there exist four integers $a, b, c, d$ such that for each $x \in \{a,b,c,d\}$, its absolute value $|x|$ is strictly greater than $M$, and they satisfy the equation
$$ \frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}=\frac{1}{abcd} $$.
One such choice of integers, for $M \ge 1$, is $a = M+1$, $b = -(M+2)$, $c = -(M^2+3M+3)$, and $d = 1-(M+1)(M+2)(M^2+3M+3)$. -/
theorem algebra_635864 (M : ℤ) (hM : M > 0) : ∃ a b c d : ℤ, (|a| > M ∧ |b| > M ∧ |c| > M ∧ |d| > M ∧ 1 / (↑a : ℝ) + 1 / b + 1 / c + 1 / d = 1 / (a * b * c * d)):= by
  -- Use the specific construction suggested in the problem statement
  use (M + 1), (-(M + 2)), (-(M ^ 2 + 3 * M + 3)), (1 - (M + 1) * (M + 2) * (M ^ 2 + 3 * M + 3))
  -- Prove |b| = |-(M+2)| > M
  -- Since M+2 > 0, we have |-(M+2)| = M+2 > M
  have h1 : |-(M + 2)| > M:= by
    rw [abs_of_neg (by linarith)]
    linarith
  -- Prove |c| = |-(M²+3M+3)| > M
  -- Since M²+3M+3 > 0, we have |-(M²+3M+3)| = M²+3M+3 > M
  have h2 : |-(M ^ 2 + 3 * M + 3)| > M:= by
    rw [abs_of_neg (by linarith only [show M ^ 2 + 3 * M + 3 > 0 by positivity])]
    linarith only [show M ^ 2 + 2 * M + 3 > 0 by positivity]
  -- Prove |d| = |1-(M+1)(M+2)(M²+3M+3)| > M
  -- Since the product (M+1)(M+2)(M²+3M+3) is much larger than 1, d is negative
  -- and its absolute value is greater than M
  have h3 : |1 - (M + 1) * (M + 2) * (M ^ 2 + 3 * M + 3)| > M:= by
    rw [abs_of_neg]
    ring_nf
    linarith only [show 5 + M * 14 + M ^ 2 * 14 + M ^ 3 * 6 + M ^ 4 > 0 by positivity]
    linarith only [show 4 + M * 15 + M ^ 2 * 14 + M ^ 3 * 6 + M ^ 4 > 0 by positivity]
  -- Now we prove all five required conditions
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Prove |a| = |M+1| = M+1 > M (since M+1 > 0)
  .
    rw [abs_of_pos (by linarith)]
    linarith
  -- Use the previously proven result for |b| > M
  .
    exact h1
  -- Use the previously proven result for |c| > M
  .
    exact h2
  -- Use the previously proven result for |d| > M
  .
    exact h3
  -- Finally, prove the main equation: 1/a + 1/b + 1/c + 1/d = 1/(abcd)
  .
    -- First establish that none of our values are zero (needed for division)
    replace h1 : -(M + 2) ≠ 0:= by
      replace h1 : |-(M + 2)| ≠ 0:= by linarith
      by_contra H
      rw [H] at h1
      simp at h1
    replace h2 : -(M ^ 2 + 3 * M + 3) ≠ 0:= by
      replace h2 : |-(M ^ 2 + 3 * M + 3)| ≠ 0:= by linarith
      by_contra H
      rw [H] at h2
      simp at h2
    replace h3 : 1 - (M + 1) * (M + 2) * (M ^ 2 + 3 * M + 3) ≠ 0:= by
      replace h3 : |1 - (M + 1) * (M + 2) * (M ^ 2 + 3 * M + 3)| ≠ 0:= by linarith
      by_contra H
      rw [H] at h3
      simp at h3
    -- Set up convenient names for our values
    set a:= -(M + 2) with ha
    set b:= -(M ^ 2 + 3 * M + 3) with hb
    set c:= 1 - (M + 1) * (M + 2) * (M ^ 2 + 3 * M + 3) with hc
    clear_value a b c
    have h4 : M + 1 ≠ 0:= by linarith
    set d:= (M + 1) with hd
    clear_value d
    -- Use field_simp to clear denominators and verify the algebraic identity
    field_simp
    -- Substitute back the original expressions and simplify
    subst a b c d
    simp
    -- The final step is pure ring algebra to verify the identity
    ring_nf
