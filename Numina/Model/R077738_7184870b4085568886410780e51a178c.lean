import Mathlib

theorem algebra_4430 {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x > y)
    (h : x^3 + 7 * y = y^3 + 7 * x) : (x, y) = (2, 1) := by
  have h1 : x^3 + 7 * y = y^3 + 7 * x := by linarith
  have h2 : (x - y) * (x^2 + x * y + y^2) = 7 * (x - y) := by
    ring_nf at h1 ⊢
    linarith
  have h3 : x - y ≠ 0 := by linarith
  have h4 : x^2 + x * y + y^2 = 7 := by 
    apply (mul_right_inj' h3).mp
    linarith
  -- Now we prove x=2 and y=1
  have h5 : y ≤ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 2), sq_nonneg (y - 1)]
  have h6 : y ≥ 1 := by linarith
  have dy : y = 1 ∨ y = 2 := by omega
  rcases dy with (h7 | h7)
  · -- y = 1
    rw [h7] at h4
    have hx' : x = 2 := by
      nlinarith [sq_nonneg (x - 2)]
    simp [hx', h7]
  · -- y = 2
    rw [h7] at h4
    -- Now we check for possible x given y = 2 
    -- x^2 + 2*x + 4 = 7
    have hx' : x ≤ 2 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1)]
    have hx'' : x ≥ 3 := by linarith [hxy, h7]
    linarith