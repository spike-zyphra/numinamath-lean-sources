import Mathlib
open Real Set

/- For the equation $\cos^2x + \sin x + a = 0$ to have a solution in the interval $x \in (0, \frac{\pi}{2}]$, the range of values for $a$ is \_\_\_\_\_\_. -/
theorem algebra_9381 {a : ℝ} :
  (∃ x ∈ Ioc 0 (π/2), cos x ^ 2 + sin x + a = 0) ↔ a ∈ Icc (-5/4) (-1) := by

  -- Expand the definitions of intervals
  simp

  -- Rewrite cos^2 x as 1 - sin^2 x
  conv =>
    lhs; congr; ext x; rhs
    rw [cos_sq' x]

  -- Split the goal into two
  constructor <;> intro h

  . -- Obtain x from the hypothesis
    obtain ⟨x, hx, h⟩ := h

    -- Simplify the expression
    replace h : a = sin x ^ 2 - sin x - 1 := by linarith

    -- Prove that sin x ∈ (0, 1]
    have h1 : 0 < sin x := by
      apply sin_pos_of_mem_Ioo
      constructor <;> linarith
    have h2 : sin x ≤ 1 := sin_le_one x

    -- Remaining trivial steps
    rw [h]
    constructor
    . linarith [sq_nonneg (sin x - 1/2)]
    . nlinarith

  . -- Rewrite the equation as (sin x - 1/2)^2 = a + 5/4
    conv =>
      congr; ext x; rhs
      rw [(by constructor <;> intro h <;> linarith : 1 - sin x ^ 2 + sin x + a = 0 ↔ (sin x - 1/2) ^ 2 = a + 5/4)]

    -- Let x = arcsin (√(a + 5/4) + 1/2)
    use arcsin (√(a + 5/4) + 1/2)

    -- Prove that √(a + 5/4) + 1/2 ≤ 1
    have h1 : √(a + 5/4) + 1/2 ≤ 1 := by
      have h1 : a + 5/4 ≤ (1/2)^2 := by linarith
      replace h1 : √(a + 5/4) ≤ 1/2 :=  sqrt_le_iff.2 ⟨by norm_num, h1⟩
      linarith

    -- Split the goal into three
    refine ⟨⟨?_, ?_⟩, ?_⟩

    . -- 0 < arcsin (√(a + 5/4) + 1/2) because 0 < √(a + 5/4) + 1/2
      apply arcsin_pos.2
      positivity

    . -- arcsin l ≤ π/2
      exact arcsin_le_pi_div_two _

    . -- sin (arcsin l) = l, if -1 ≤ l ≤ 1
      rw [sin_arcsin (by linarith [sqrt_nonneg (a + 5/4)]) h1]
      simp
      -- √x ^ 2 = x, if x ≥ 0
      exact sq_sqrt (by linarith)
