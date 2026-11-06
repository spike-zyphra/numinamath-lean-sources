import Mathlib

open Real

theorem calculus_12621 {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ x, f x = x ^ 2 + 2 * x * deriv f 2) :
    f (-1) > f 1 := by
  let f2 := deriv f 2
  -- We define $f_2 := f'(2)$
  have eq1 : deriv f = fun x => 2 * x + 2 * f2 := by
    funext x
    have h1 : f = fun x => x^2 + 2 * x * f2 := by
      funext x
      specialize h x
      simpa using h
    rw [h1]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, mul_comm]
    <;> field_simp <;> ring_nf
    <;> simp_all
    <;> ring
  -- Solving for the derivation at point 2
  have h2 : f2 = -4 := by
    have eq2' : deriv f 2 = 2 * (2 : ℝ) + 2 * f2 := by
      rw [eq1]
    rw [show deriv f 2 = f2 by simp [f2]] at eq2'
    linarith
  -- Now we get f from its definition
  have eq3 : f = fun x => x^2 + 2 * x * f2 := by
    funext x
    specialize h x
    simpa using h
  -- Substitute f2 = -4 into f
  rw [show f2 = -4 by linarith [h2]] at eq3
  -- Calculate f(-1) and f(1)
  have h3 : f (-1) = 9 := by
    rw [eq3]
    norm_num
  have h4 : f 1 = -7 := by
    rw [eq3]
    norm_num
  linarith [h3, h4]