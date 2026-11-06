import Mathlib

theorem algebra_73305 {x y z : ℝ} (h₀ : x^2 - y * z = 2) (h₁ : y^2 - z * x = 2)
    (h₂ : z^2 - x * y = 2) :
    x * y + y * z + z * x = -2 := by
  have h3 : (x - y) * (x + y + z) = 0 := by
    nlinarith
  
  have h4 : (y - z) * (x + y + z) = 0 := by
    nlinarith

  have h5 : (z - x) * (x + y + z) = 0 := by
    nlinarith
  
  by_cases h : x + y + z = 0
  · -- If x + y + z = 0, then we can compute $xy + yz + zx.
    have h3' : x^2 + y^2 + z^2 = x * y + y * z + z * x + 6 := by
      nlinarith
    nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · -- x + y + z ≠ 0
    have hxy : x = y := by
      apply_fun (λ w => w / (x + y + z)) at h3
      field_simp [h] at h3
      linarith

    have hyz : y = z := by
      apply_fun (λ w => w / (x + y + z)) at h4
      field_simp [h] at h4
      linarith

    have hxz : x = z := by
      linarith [hxy, hyz]

    nlinarith [hxz, hxy]