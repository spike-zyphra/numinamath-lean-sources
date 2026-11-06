import Mathlib

/- If $m, n$ and $p$ are positive integers with $m+\frac{1}{n+\frac{1}{p}}=\frac{17}{3}$, the value of $n$ is
(A) 3
(B) 4
(C) 1
(D) 17
(E) 13 -/
theorem algebra_274101 {m n p : ℤ} (hm : m > 0) (hn : n > 0) (hp : p > 0)
    (h : m + 1 / (n + 1 / p : ℝ) = 17 / 3) : n = 1 := by 
  have nge : n ≥ 1 := by linarith
  have pge : p ≥ 1 := by linarith
  have ineq1 : n + 1 / (p : ℝ) > 1 := by 
    have ineq_aux : 1 / (p : ℝ) > 0 := by positivity
    have nge' : (n : ℝ) ≥ 1 := by norm_cast
    nlinarith
  -- 1 / (n + 1 / (p : ℝ)) > 0
  have ineq2 : 1 / (n + 1 / (p : ℝ)) > 0  := by 
    positivity
  have ineq3 : 1 / (n + 1 / (p : ℝ)) < 1 := by 
    apply div_lt_iff₀ (by positivity) |>.mpr
    linarith
  -- m < m + 1 / (n + 1 / (p : ℝ)) < m + 1
  have ineq_m : m + 1 / (n + 1 / (p : ℝ)) > m := by linarith
  have ineq_m2 : m + 1 / (n + 1 / (p : ℝ)) < m + 1 := by linarith
  rw [h] at ineq_m
  rw [h] at ineq_m2
  have meq : m = 5 := by 
    have ineq_aux : 17 / 3 < (6 : ℝ) := by norm_num
    have mle : m < 6 := by 
      obtain mle' := lt_trans ineq_m ineq_aux
      norm_cast at mle'
    interval_cases m
    norm_num at ineq_m2
    norm_num at ineq_m2
    norm_num at ineq_m2
    norm_num at ineq_m2
    rfl
  -- 1 / (n + 1 / (p : ℝ)) = 2 / (3 : ℝ)
  rw [meq] at h
  have eq_aux : 1 / (n + 1 / (p : ℝ)) = 2 / (3 : ℝ) := by nlinarith
  have eq_aux1 : (n + 1 / (p : ℝ)) = 3 / (2 : ℝ) := by 
    rw [div_eq_div_iff] at eq_aux
    nlinarith
    positivity
    positivity
  -- n < (n + 1 / (p : ℝ)) ≤ n + 1
  have ineq3 : (n + 1 / (p : ℝ)) > n := by 
    have ineq_aux : 1/ (p : ℝ) > 0 := by positivity
    nlinarith
  have ineq4 : (n + 1 / (p : ℝ)) ≤  n + 1 := by 
    have ineq_aux : 1 / (p : ℝ) ≤ 1 := by 
      refine (div_le_iff₀ ?_).mpr ?_
      positivity
      norm_cast
      simpa
    nlinarith
  rw [eq_aux1] at ineq3
  rw [eq_aux1] at ineq4
  have ineq5 : 3 / (2 : ℝ) < 2 := by norm_num
  obtain ineq6 := lt_trans ineq3 ineq5
  norm_cast at ineq6
  interval_cases n
  rfl

