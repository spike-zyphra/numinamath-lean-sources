import Mathlib

open Real Set

/- If $a>0$, $b>0$, and $a+2b=6$, then the maximum value of $\ln a+2\ln b$ is ___          ___. -/
theorem algebra_8521 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + 2 * b = 6) :
    log a + 2 * log b ≤ log 8 := by
  have h1 : log a + 2 * log b = log (a * (b ^ 2)) := by
    have h2 : log a + 2 * log b = log a + log (b ^ 2) := by
      simp [log_pow]
    rw [h2]
    rw [← log_mul (by positivity) (by positivity)]

  rw [h1]

  have h2 : a * (b ^ 2) ≤ 8 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), 
      sq_nonneg (a - 2 * b), sq_nonneg (a + 2 * b - 6),
      mul_pos ha hb
    ]

  have h3 : log (a * (b ^ 2)) ≤ log 8 := by
    apply log_le_log
    positivity
    nlinarith [h2]

  linarith