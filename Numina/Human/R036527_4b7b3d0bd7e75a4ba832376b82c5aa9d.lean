import Mathlib

/- 17. A real-valued function $\mathrm{f}$ satisfies the relation
$$
f\left(x^{2}+x\right)+2 f\left(x^{2}-3 x+2\right)=9 x^{2}-15 x
$$
for all real values of $x$. Find $f(2011)$. -/
theorem algebra_100669 {f : ℝ → ℝ} (h : ∀ x, f (x ^ 2 + x) + 2 * f (x ^ 2 - 3 * x + 2) = 9 * x ^ 2 - 15 * x) :
    f 2011 = 6029 := by
  -- Define four special values of x that will help us solve the problem
  have h1 := h ((-1 + Real.sqrt 8045) / 2)
  have h2 := h ((-1 - Real.sqrt 8045) / 2)
  have h3 := h ((3 + Real.sqrt 8045) / 2)
  have h4 := h ((3 - Real.sqrt 8045) / 2)

  -- Prove that when x = (-1 + √8045)/2, x² + x = 2011
  have eq1 : ((-1 + Real.sqrt 8045) / 2) ^ 2 + ((-1 + Real.sqrt 8045) / 2) = (2011 : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (-1 + √8045)/2, x² - 3x + 2 = 2009 + 4*((3 - √8045)/2)
  have eq2 : ((-1 + Real.sqrt 8045) / 2) ^ 2 - 3 * ((-1 + Real.sqrt 8045) / 2) + 2 = (2009 + 4 * ((3 - Real.sqrt 8045) / 2) : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (-1 - √8045)/2, x² + x = 2011
  have eq3 : ((-1 - Real.sqrt 8045) / 2) ^ 2 + ((-1 - Real.sqrt 8045) / 2) = (2011 : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (-1 - √8045)/2, x² - 3x + 2 = 2009 + 4*((3 + √8045)/2)
  have eq4 : ((-1 - Real.sqrt 8045) / 2) ^ 2 - 3 * ((-1 - Real.sqrt 8045) / 2) + 2 = (2009 + 4 * ((3 + Real.sqrt 8045) / 2) : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (3 + √8045)/2, x² + x = 2009 + 4*((3 + √8045)/2)
  have eq5 : ((3 + Real.sqrt 8045) / 2) ^ 2 + ((3 + Real.sqrt 8045) / 2) = (2009 + 4 * ((3 + Real.sqrt 8045) / 2) : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (3 + √8045)/2, x² - 3x + 2 = 2011
  have eq6 : ((3 + Real.sqrt 8045) / 2) ^ 2 - 3 * ((3 + Real.sqrt 8045) / 2) + 2 = (2011 : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (3 - √8045)/2, x² + x = 2009 + 4*((3 - √8045)/2)
  have eq7 : ((3 - Real.sqrt 8045) / 2) ^ 2 + ((3 - Real.sqrt 8045) / 2) = (2009 + 4 * ((3 - Real.sqrt 8045) / 2) : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Prove that when x = (3 - √8045)/2, x² - 3x + 2 = 2011
  have eq8 : ((3 - Real.sqrt 8045) / 2) ^ 2 - 3 * ((3 - Real.sqrt 8045) / 2) + 2 = (2011 : ℝ) := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  -- Substitute the proven equalities into the functional equations
  rw [eq1, eq2] at h1
  rw [eq3, eq4] at h2
  rw [eq6, eq5] at h3
  rw [eq8, eq7] at h4

  -- Simplify the resulting equations
  ring_nf at h1 h2 h3 h4

  -- Solve the system of equations to find f(2011) = 6029
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 8045 by norm_num)]
