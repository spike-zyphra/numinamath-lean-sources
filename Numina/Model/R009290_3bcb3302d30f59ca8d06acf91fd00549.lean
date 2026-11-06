import Mathlib

theorem algebra_12824  :
    IsGreatest {c : ℝ | ∃ x, -2 = x ^ 2 + 3 * x + c} (1 / 4) := by
  constructor
  · -- Show 1/4 is in the set
    use -3 / 2
    norm_num
  · -- Show 1/4 is greatest element in the set
    intros c hc
    rcases hc with ⟨x, hx⟩
    -- From -2 = x^2 + 3 * x + c, we can write x^2 + 3 * x + (c + 2) = 0
    have h1 : x ^ 2 + 3 * x + (c + 2) = 0 := by linarith
    -- Completing the square, (x + 3/2)^2 = 1/4 - c
    have h2 : (x + 3/2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    -- Therefore, 1/4 - c ≥ 0, which leads to c ≤ 1/4
    nlinarith [sq_nonneg (x + 3/2)]