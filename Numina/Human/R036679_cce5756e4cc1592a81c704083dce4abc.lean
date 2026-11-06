import Mathlib 

/-Let $x, y, z$ be positive real numbers. Prove that:

$$
\left(x^{2}+y+1\right)\left(x^{2}+z+1\right)\left(y^{2}+z+1\right)\left(y^{2}+x+1\right)\left(z^{2}+x+1\right)\left(z^{2}+y+1\right) \geq(x+y+z)^{6}
$$-/
theorem number_theory_879 (x y z : ℝ) (xpos : 0 < x) (ypos : 0 < y) (zpos : 0 < z): 
  (x^2 + y + 1) * (x^2 + z + 1) * (y^2 + z + 1) * (y^2 + x + 1) * (z^2 + x + 1) * (z^2 + y + 1) ≥  (x + y + z)^ 6 := by 
    -- We have
    -- $$
    -- \begin{gathered}
    -- \left(x^{2}+y+1\right)\left(z^{2}+y+1\right) \geq(x+y+z)^{2} \Leftrightarrow \\
    -- x^{2} z^{2}+x^{2} y+x^{2}+y z^{2}+y^{2}+y+z^{2}+y+1 \geq x^{2}+y^{2}+z^{2}+2 x y+2 y z+2 z x \Leftrightarrow \\
    -- \left(x^{2} z^{2}-2 z x+1\right)+\left(x^{2} y-2 x y+y\right)+\left(y z^{2}-2 y z+y\right) \geq 0 \Leftrightarrow \\
    -- (x z-1)^{2}+y(x-1)^{2}+y(z-1)^{2} \geq 0
    -- \end{gathered}
    -- $$

    -- which is correct.

    -- Using the same reasoning we get:

    -- $$
    -- \begin{aligned}
    -- & \left(x^{2}+z+1\right)\left(y^{2}+z+1\right) \geq(x+y+z)^{2} \\
    -- & \left(y^{2}+x+1\right)\left(z^{2}+x+1\right) \geq(x+y+z)^{2}
    -- \end{aligned}
    -- $$
    have h1 : (x^2 + y + 1) * (z^2 + y + 1) ≥ (x + y + z)^2 := by 
      ring_nf
      suffices (x*z - 1)^2 + y * (x - 1)^2 + y * (z - 1)^2 ≥ 0 by linarith 
      positivity
    have h2 : (x^2 + z + 1) * (y^2 + z + 1) ≥ (x + y + z)^2:= by 
      ring_nf
      suffices (x*y - 1)^2 + z * (x - 1)^2 + z * (y - 1)^2 ≥ 0 by linarith
      positivity
    have h3 : (y^2 + x + 1) * (z^2 + x + 1) ≥ (x + y + z)^2 := by 
      ring_nf
      suffices (y*z - 1)^2 + x * (y - 1)^2 + x * (z - 1)^2 ≥ 0 by linarith
      positivity
        
    -- Multiplying these three inequalities we get the desired result. Equality is attained at $x=y=z=1$.
    suffices ((x^2 + y + 1) * (z^2 + y + 1)) * ((x^2 + z + 1) * (y^2 + z + 1)) * ((y^2 + x + 1) * (z^2 + x + 1)) ≥  ((x + y + z)^ 6:ℝ ) by 
      convert this using 1 
      linarith 
    rw [show (x + y + z)^6 = (x + y + z)^2 * (x + y + z)^2 * (x + y + z)^2 by ring]
    apply mul_le_mul
    apply mul_le_mul
    any_goals assumption 
    any_goals positivity 


