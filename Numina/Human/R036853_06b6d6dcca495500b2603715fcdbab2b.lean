import Mathlib

open Real Set

/-Jonathon is given the following problem: Let $a$ and $b$ be positive real numbers such that $a + b = 1.$  Find the minimum value of
\[\left( a + \frac{1}{a} \right)^2 + \left( b + \frac{1}{b} \right)^2.\]Jonathon reasons as follows: By AM-GM,
\[a + \frac{1}{a} \ge 2,\]and
\[b + \frac{1}{b} \ge 2,\]so
\[\left( a + \frac{1}{a} \right)^2 + \left( b + \frac{1}{b} \right)^2 \ge 2^2 + 2^2 = 8.\]He concludes that the minimum value is 8, but this answer is incorrect.  What is the minimum value?

As a bonus, determine where Jonathon went wrong.-/
theorem algebra_22090 :
    IsLeast {m | ∃a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ m = (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2} (25 / 2) := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  -- show m = 25 / 2 when a = b = 1 / 2
  . use (1 / 2)
    simp
    use (1 / 2)
    norm_num
  -- show that m ≥ 25 / 2
  . intro m a ha b hb h hm
    -- show the inequality of AM-QM
    have am_qm (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
      linarith only [show 0 ≤ (x - y) ^ 2 by positivity]
    -- show the inequality of AM-HM
    have am_hm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 4 / (x + y) ≤ 1 / x + 1 / y := by
      calc
        4 / (x + y) = (4 * x * y) * (1 / (x * y * (x + y))) := by field_simp; ring_nf
        _ ≤ (x + y) ^ 2 * (1 / (x * y * (x + y))) := by
          apply mul_le_mul
          -- show 4 * x * y ≤ (x + y) ^ 2
          linarith only [show 0 ≤ (x - y) ^ 2 by positivity]
          linarith
          all_goals positivity
        _ = 1 / x + 1 / y := by field_simp; ring_nf
    -- get the inequality that we want to use
    have ineq1 := am_qm (a + 1 / a) (b + 1 / b)

    have ineq2 := am_hm a b ha hb
    -- do calculation that m ≥ 25 / 2
    have _ : m ≥ 25 / 2 := by
      calc
        m = (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 := by rw [hm]; ring_nf
        _ = 2 * ((a + 1 / a) ^ 2 + (b + 1 / b) ^ 2) * (1 / 2) := by ring_nf
        _ ≥ (a + 1 / a + (b + 1 / b)) ^ 2 * (1 / 2) := by apply mul_le_mul; exact ineq1; norm_num; norm_num; positivity
        _ = (a + b + 1 / a + 1 / b) ^ 2 * (1 / 2) := by ring_nf
        _ = (1 + 1 / a + 1 / b) ^ 2 * (1 / 2) := by rw [h]
        _ ≥ (1 + 4 / (a + b)) ^ 2 * (1 / 2) := by
          -- simplify to show that 4 / (a + b) ≤ 1 / a + 1 / b
          apply mul_le_mul
          apply pow_le_pow_left₀
          pick_goal 2
          rw [add_assoc]
          apply add_le_add
          pick_goal 2
          exact ineq2
          -- show the rest condition
          all_goals norm_num
          all_goals positivity
        _ = (1 + 4 / 1) ^ 2 * (1 / 2) := by rw [h]
        _ = 25 / 2 := by norm_num

    linarith