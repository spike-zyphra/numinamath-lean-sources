import Mathlib

/- It takes four painters working at the same rate $1.25$ work-days to finish a job. If only three painters are available, how many work-days will it take them to finish the job, working at the same rate? Express your answer as a mixed number. -/
theorem algebra_10408 {D : ℝ} (h : 4 * 1.25 = 3 * D) : D = 1 + 2 / 3 := by
  field_simp at h ⊢
  norm_num at h
  linarith only [h]
