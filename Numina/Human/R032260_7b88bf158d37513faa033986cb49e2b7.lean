import Mathlib

/-- 4. Solve the system of equations
  $\left\{\begin{array}{l}y+\sqrt{y-3 x}+3 x=12, \\ y^{2}+y-3 x-9 x^{2}=144 .\end{array}\right.$ -/
theorem algebra_162284 (x y : ℝ) (le : 3 * x ≤ y) (h₀ : y + Real.sqrt (y - 3 * x) + 3 * x = 12)
    (h₁ : y ^ 2 + y - 3 * x - 9 * x ^ 2 = 144) :
    (x = -24 ∧ y = 72) ∨ (x = -4 / 3 ∧ y = 12) := by
  -- Answer: (-24;72), (-4/3,12).
  -- Solution: Let u = sqrt(y-3*x), v=y+3x.
  let u := Real.sqrt (y-3*x)
  let v := y + 3 * x
  -- u >= 0 by assumption.
  have u_pos : u ≥ 0 := by unfold u; positivity
  have u_sq : u^2 = y - 3 * x := by apply Real.sq_sqrt; linarith
  -- Then the system takes the form u + v = 12; u^2v + u^2 = 144, 
  have u_v_add : u + v = 12 := by unfold u v; linarith
  have squares : u^2 * v + u ^ 2 = 144 := by rw[u_sq]; unfold v; rw[← h₁]; ring
  -- equivalently v = 12 - u; u^2 (12-u) + u^2 = 144.
  have v_eq : v = 12 - u := by linarith
  have u_eq : u^2 * (12 - u) + u^2 = 144 := by rw[← squares, v_eq]
  -- From the second equation of the last system, it follows that u^3-13u^2+144=0.
  have u_eq' : u^3 - 13 * u^2 + 144 = 0 := by linarith
  -- By selecting the integer root u=4 and factoring out (u-4), we get
  -- (u-4)(u^2-9-36) = 0,
  have u_eq'' : (u-4) * (u - 12) * (u - (-3)) = 0 := by linarith
  -- from which u = -3, u = 4 or u = 12.
  simp only [mul_eq_zero] at u_eq''
  rw[sub_eq_zero, sub_eq_zero, sub_eq_zero] at u_eq''
  rcases u_eq'' with ((eq|eq)|eq)
  -- For u = 4, we get v = 8.
  · rw[eq] at v_eq
    unfold u at eq
    unfold v at v_eq
    -- Then y - 3x = 16, y + 3x = 8, equivalently 2y=24, 6x = -8,
    rw[Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)] at eq
    -- or y = 12, x = -4/3.
    have : y = 12 := by linarith
    have : x = -4/3 := by linarith
    tauto
    -- For u = 12, we get v = 0.
  · rw[eq] at v_eq
    unfold u at eq
    unfold v at v_eq
    -- Then y - 3x = 144, y + 3x = 0, equivalently 2y=144, -6x = 144;
    rw[Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)] at eq
    -- or y = 72, x = -24.
    have : y = 72 := by linarith
    have : x = -24 := by linarith
    tauto
    -- u = -3 is not suitable, since it is a square root hence nonnegative.
  · rw[eq] at u_pos
    norm_num at u_pos