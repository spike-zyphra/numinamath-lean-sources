import Mathlib

/-What is the maximum value of $-x^2- 8x + 12$?-/
theorem algebra_20143 : IsGreatest {-x^2 - 8 * x + 12 | x : ℝ} 28 := by
  -- simplify the desired conclusion
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  -- show that ∃x, -x^2-8x+10 = 28
  . use (-4)
    norm_num
  -- show that -x ^ 2 - 8 * x + 12 ≤ 28
  . intro x
    calc
      -x ^ 2 - 8 * x + 12 = -(x + 4) ^ 2 + 28 := by ring_nf
      _ ≤ 28 := by linarith only [show (x + 4) ^ 2 ≥ 0 by positivity]
