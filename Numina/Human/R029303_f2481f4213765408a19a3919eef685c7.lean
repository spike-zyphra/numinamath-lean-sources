import Mathlib

/- Given that $z$ is a complex number, $z+2i$ and $\frac{z}{2-i}$ are both real numbers, where $i$ is the imaginary unit. Find the absolute value of the complex number $|z|=$ \_\_\_\_\_\_. -/
theorem algebra_9201 {z : ℂ} (hz : ∃ r : ℝ, z + 2 * .I = r) (hz' : ∃ r : ℝ, z / (2 - .I) = r) :
    Complex.abs z = 2 * Real.sqrt 5 := by
  -- Let z = a + bi
  obtain ⟨a, b⟩ := z

  -- Im (z + 2i) = Im (z / (2 - i)) = 0
  obtain ⟨r₁, hr₁⟩ := hz
  obtain ⟨r₂, hr₂⟩ := hz'
  apply_fun Complex.im at hr₁
  apply_fun Complex.im at hr₂

  -- Simplify the equations using Complex.div_im and Complex.normSq
  rw [Complex.div_im] at hr₂
  simp [Complex.normSq] at hr₁ hr₂
  norm_num at hr₂

  -- Solve the equations, and we get a = 4, b = -2
  have hb : b = -2 := by linarith
  have ha : a = 4 := by linarith

  -- Trivial simplification
  simp [Complex.abs, ha, hb]
  norm_num
  rw [(by simp :2 = √(2*2)), ←Real.sqrt_mul (by norm_num)]
  norm_num
