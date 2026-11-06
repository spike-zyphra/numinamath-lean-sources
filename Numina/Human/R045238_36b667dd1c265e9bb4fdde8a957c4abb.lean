import Mathlib

open Real

/- 27. The logarithmic mean of two positive numbers $x$ and $y$ is defined as:
$$\begin{array}{c}
L(x, y)=\frac{x-y}{\ln x-\ln y}, x \neq y \\
L(x, x)=x
\end{array}$$

Prove: $L(x, y) \leqslant \frac{x+y}{2}$. -/
theorem inequalities_603168 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (if x = y then x else (x - y) / (log x - log y)) ≤ (x + y) / 2 := by
  -- The case x = y is trivial.
  split_ifs with h
  . simp [h]
  -- WLOG, assume x < y.
  wlog hxy : x < y with H
  {
    -- If y < x, then we can swap x and y and use the same proof.
    rw [not_lt] at hxy
    replace hxy : y < x := lt_of_le_of_ne hxy (Ne.symm h)
    specialize H y x hy hx (Ne.symm h) hxy
    rw [← neg_div_neg_eq] at H
    convert H using 2 <;> ring
  }
  -- Main lemma: Cauchy-Schwarz inequality for integrals
  -- (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2)
  -- For simplicity, we assume f and g are continuous functions on ℝ.
  have cauchy (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
      (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
    -- The integral of (α * f x + g x) ^ 2 is non-negative for any α since the integrand is a square.
    have H (α : ℝ) : 0 ≤ ∫ x in a..b, (α * f x + g x) ^ 2 := intervalIntegral.integral_nonneg hab fun x hx => sq_nonneg _
    -- Expand the integrand and rearrange terms.
    have h₀ (α : ℝ) (x : ℝ) : (α * f x + g x) ^ 2 = α ^ 2 * f x ^ 2 + 2 * α * (f x * g x) + g x ^ 2 := by ring
    simp [h₀] at H
    replace H (α : ℝ) : 0 ≤ (∫ x in a..b, f x ^ 2) * (α * α) + (2 * ∫ x in a..b, f x * g x) * α + ∫ x in a..b, g x ^ 2 := by
      specialize H α
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
      linarith only [H]
      -- Some lemmas about integrability.
      -- They all hold since the functions are continuous.
      all_goals
        apply Continuous.intervalIntegrable
        continuity
    -- The discriminant of the quadratic must be non-positive.
    apply discrim_le_zero at H
    simp [discrim] at H
    -- We get the desired inequality.
    linarith only [H]
  -- Now we apply the main lemma to the functions exp and 1 with the interval [log x, log y].
  let f := exp
  let g : ℝ → ℝ := 1
  specialize cauchy (log x) (log y) (le_of_lt (log_lt_log hx hxy)) f g continuous_exp continuous_one
  -- Simplify the integrals.
  simp [f, g, exp_log hx, exp_log hy] at cauchy
  -- Calculate the integral of exp^2.
  have H : ∫ (x : ℝ) in log x..log y, exp x ^ 2 = (y ^ 2 - x ^ 2) / 2 := by
    -- exp^2 is the derivative of exp^2 / 2.
    have H : (fun x => exp x ^ 2) = deriv (fun x => exp x ^ 2 / 2) := by
      ext x
      simp
      ring
    -- Let's use the fundamental theorem of calculus.
    convert intervalIntegral.integral_deriv_eq_sub (f := fun x => exp x ^ 2 / 2) (a := log x) (b := log y) (by simp) (Continuous.intervalIntegrable ?_ _ _) using 1
    . congr
    . simp [exp_log hx, exp_log hy]
      ring
    . rw [← H]
      clear H
      continuity
  rw [H] at cauchy
  -- Now the inequality is (y - x) ^ 2 ≤ (y ^ 2 - x ^ 2) / 2 * (log y - log x)
  -- We can divide both sides by (y - x).
  replace cauchy : (y - x) * (y - x) ≤ (y - x) * ((x + y) * (log y - log x) / 2) := by convert cauchy using 1 <;> ring
  rw [mul_le_mul_left (sub_pos.mpr hxy)] at cauchy
  -- We cancel the denominators in the goal.
  rw [div_le_iff_of_neg (sub_neg.mpr (log_lt_log hx hxy))]
  -- We get the desired inequality.
  linarith only [cauchy]
