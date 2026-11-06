import Mathlib

/- Zij $n$ een positief geheel getal. Bewijs dat $n^{2}+n+1$ niet te schrijven is als het product van twee positieve gehele getallen die minder dan $2 \sqrt{n}$ van elkaar verschillen. -/
theorem number_theory_604522 (n : ℤ) (hn : n > 0) :
    ¬∃ (a b : ℤ), a > 0 ∧ b > 0 ∧ a * b = n^2 + n + 1 ∧ |(a : ℝ) - b| < 2 * Real.sqrt n := by
  intro h
  rcases h with ⟨a, b, hapos, hbpos, heq, hle⟩
  -- $$ (a+b)^{2}=(a-b)^{2}+4 a b \\geq 4 a b=4 n^{2}+4 n+4 > 4 n^{2}+4 n+1=(2 n+1)^{2} . $$
  have hineq1 : (a + b) ^ 2 > (2*n + 1) ^ 2 := by
    calc
      _ = (a-b)^2 + 4 * (a * b) := by ring_nf
      _ ≥ 4 * (a * b) := by
        have : (a-b)^2 ≥ 0 := sq_nonneg (a - b)
        linarith
      _ = 4*n^2 + 4*n + 4 := by
        rw [heq]
        ring_nf
      _ > 4*n^2 + 4*n + 1 := by linarith
      _ = _ := by ring
  -- Since $(a+b)^{2}$ is a square, we have $(a+b)^{2} \\geq(2 n+2)^{2}$.
  have hineq2 : a + b ≥ 2*n + 2 := by nlinarith
  -- $$ (a-b)^{2}=(a+b)^{2}-4 a b \\geq(2 n+2)^{2}-4\\left(n^{2}+n+1\\right)=4 n $$
  have hineq3 : (a - b) ^ 2 ≥ 4 * n := by
    calc
      _ = (a + b) ^ 2 - 4 * (a * b) := by ring_nf
      _ ≥ (2*n + 2) ^ 2 - 4 * (n^2+n+1) := by
        rw [heq]
        nlinarith
      _ = _ := by ring_nf
  -- By contradiction, we know that ((a - b)^2 < 4n).
  have hineq4 : (a - b) ^ 2 < 4 * n := by
    rw [Mathlib.Tactic.Qify.intCast_lt]
    rw [Mathlib.Tactic.Rify.ratCast_lt]
    calc
      _ = |(a : ℝ) - b| ^ 2 := by simp
      _ < (2 * √n) ^ 2 := by
        have hpos1 : |(a:ℝ) - ↑b| ≥ 0 := by exact abs_nonneg ((a:ℝ) - b)
        have hpos2 : 2 * √(n:ℝ) ≥ 0 := by
          have : √(n:ℝ) > 0 := by
            apply Real.sqrt_pos_of_pos
            norm_cast
          linarith
        refine sq_lt_sq.mpr ?_
        have h1 : |(|(a:ℝ) - ↑b|)| = |(a:ℝ) - b| := by apply abs_of_nonneg hpos1
        have h2 :|2 * √↑n| = 2 * √↑n := by apply abs_of_nonneg hpos2
        rw [h1, h2]
        linarith
      _ = _ := by
        ring_nf
        rw [Real.sq_sqrt]
        · norm_cast
        · norm_cast
          linarith
  linarith
