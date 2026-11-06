import Mathlib

/- If $15\%$ of $N$ is $45\%$ of 2003, what is the value of $N$? -/
theorem algebra_13920 {N : ℝ} (hN : N ≠ 0) (h : 15 / 100 * N = 45 / 100 * 2003) :
    N = 6009 := by
  field_simp at h
  linarith