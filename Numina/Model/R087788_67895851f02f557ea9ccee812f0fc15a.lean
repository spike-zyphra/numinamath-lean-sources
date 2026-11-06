import Mathlib

theorem algebra_4096
  {x y z : ℝ}
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0)
  (h1 : 1/x + 1/y + 1/z = 1)
  (h2 : 1/x^2 + 1/y^2 + 1/z^2 = 1) :
  x + y + z = 0 := by
  have eq1 : x * y + y * z + z * x = x * y * z := by
    field_simp [hx, hy, hz] at h1 ⊢
    linarith
  
  have eq2 : (x * y)^2 + (y * z)^2 + (z * x)^2 = (x * y * z)^2 := by
    field_simp [hx, hy, hz] at h2 ⊢
    linarith
  
  have eq3 : (x * y + y * z + z * x)^2 = (x * y * z)^2 := by
    rw [eq1]

  have eq4 : (x * y)^2 + (y * z)^2 + (z * x)^2 + 2 * (x * y * z) * (x + y + z) = (x * y * z)^2 := by
    have h : (x * y + y * z + z * x)^2 = (x * y)^2 + (y * z)^2 + (z * x)^2 + 2 * (x * y * z) * (x + y + z) := by
      ring
    linarith [eq3, h]

  -- Combining eq2 with eq4 to derive $2(x*y*z)(x+y+z) = 0$
  have eq5 : 2 * (x * y * z) * (x + y + z) = 0 := by
    nlinarith

  -- Since $x*y*z ≠ 0$, since $x,y,z ≠ 0$
  have hxyz : x * y * z ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact hx
    exact hy
    exact hz

  -- Since $2 * (x * y * z) * (x + y + z) = 0$ and $x * y * z ≠ 0$, implies $x + y + z = 0$
  have h : x + y + z = 0 := by
    apply_fun (λ k : ℝ => k / (2 * (x * y * z))) at eq5
    field_simp [show x * y * z ≠ 0 by
      exact hxyz
    ] at eq5 ⊢
    all_goals linarith
  exact h