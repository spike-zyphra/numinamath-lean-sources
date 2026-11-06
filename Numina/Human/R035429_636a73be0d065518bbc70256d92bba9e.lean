import Mathlib

/- 13. [9] Suppose $x, y$, and $z$ are real numbers greater than 1 such that

$$

\begin{aligned}
x^{\log _{y} z} & =2, \\
y^{\log _{y} x} & =4, \text { and } \\
z^{\log _{x} y} & =8 .
\end{aligned}

$$


Compute $\log _{x} y$. -/
theorem algebra_182922 (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z)
    (h₁ : x ^ Real.logb y z = 2) (h₂ : y ^ Real.logb z x = 4) (h₃ : z ^ Real.logb x y = 8) :
    Real.logb x y = Real.sqrt 3 := by
  -- express all logs as division of natural log
  rw [Real.logb]
  -- express the equations with only natural logs
  have aux {a b c d} (ha: 1 < a) (h : a ^ (Real.logb b c) = d) : Real.log a * Real.log c / Real.log b = Real.log d := by
    have : Real.log (a ^ Real.logb b c) = Real.log d := by rw [h]
    rw [Real.log_rpow (show 0 < a by linarith), Real.logb] at this
    linear_combination this
  replace h₁ := aux hx h₁
  replace h₂ := aux hy h₂
  replace h₃ := aux hz h₃
  -- show the logs are positive
  have hx' : 0 < Real.log x := Real.log_pos hx
  have hy' : 0 < Real.log y := Real.log_pos hy
  have hz' : 0 < Real.log z := Real.log_pos hz
  -- now multiply h₁ h₂ and h₂ h₃, from these we get (log x)^2 and (log y)^2
  have hx'' : (Real.log x * Real.log z / Real.log y) * (Real.log y * Real.log x / Real.log z) = Real.log 2 * Real.log 4 := by
    rw [h₁, h₂]
  convert_to (Real.log x)^2 = Real.log 2 * Real.log 4 at hx''
  . field_simp
    ring
  have hy'' : (Real.log y * Real.log x / Real.log z) * (Real.log z * Real.log y / Real.log x) = Real.log 4 * Real.log 8 := by
    rw [h₂, h₃]
  convert_to (Real.log y)^2 = Real.log 4 * Real.log 8 at hy''
  . field_simp
    ring
  -- we'll prove squared version of target
  apply sq_eq_sq₀ (by positivity) (by positivity) |>.mp
  simp
  -- plug in values of squares of logs and show that the equation is an idnentity
  rw [div_pow, hx'', hy'']
  have : 0 < Real.log 4 := by positivity
  field_simp
  rw [show (8:ℝ) = 2 ^ 3 by norm_num]
  rw [Real.log_pow]
  ring