import Mathlib

/- A point $(3\sqrt{5},d+3)$ is $3d$ units away from the origin. What is the smallest possible value of $d$? -/
theorem algebra_14299 (d : ℝ) (h : d ≥ 0) (hdist : Real.sqrt ((3 * Real.sqrt 5) ^ 2 + (d + 3) ^ 2) = 3 * d) :
    d = 3 := by
  -- The above formulation is due to distance formula.
  replace hdist : (3 * Real.sqrt 5) ^ 2 + (d + 3) ^ 2 = (3 * d) ^ 2 := by
    rw [<-@Real.sq_sqrt ((3 * Real.sqrt 5) ^ 2 + (d + 3) ^ 2)]
    rw [hdist]
    nlinarith
  ring_nf at hdist
  simp [show Real.sqrt 5 ^ 2 = 5 by rw [Real.sq_sqrt]; norm_num] at hdist
  replace hdist : (4 * d + 9) * (d - 3) = 0 := by
    calc
      (4 * d + 9) * (d - 3) = d ^ 2 * 4 - d * 3 - 27 := by ring_nf
      _ = 0 := by linarith only [hdist]
  rw [mul_eq_zero] at hdist
  obtain hdist | hdist := hdist
  -- We have d ≥ 0 and 4 * d + 9 = 0, which is impossible.
  linarith
  -- We have d - 3 = 0, hence d = 3.
  linarith
