import Mathlib


/-
Solve the following system of equations for $w$.

$$
\begin{aligned}
& 2 w+x+y+z=1 \\
& w+2 x+y+z=2 \\
& w+x+2 y+z=2 \\
& w+x+y+2 z=1
\end{aligned}
$$
-/
theorem algebra_608429 (w x y z : ℝ) (h₀ : 2*w+x+y+z=1) (h₁ : w+2*x+y+z=2)  (h₂ : w+x+2*y+z=2)  (h₃ : w+x+y+2*z=1) : w  = -1/5 := by
  
  -- Add all equations
  have hsum: 5* w + 5 * x + 5 *y + 5* z = 6 := by linarith
  
  -- Simplify to get one equation in terms of sum of variables
  have hsum': w + x + y +z = 6/5 := by linarith

  calc
  --  Note that w = (2*w + x + y + z) - hsum, the result is trivailty obtained.
    _ = 2*w + x + y + z - (w +x+y+z) := by ring_nf
    _ = 1 - 6/5 := by rw [h₀, hsum']
    _ = _ := by norm_num