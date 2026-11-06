import Mathlib

theorem algebra_131590 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : 3 * x + 2 * y = z) (h2 : 3 / x + 1 / y = 2 / z) :
    ∃ n : ℤ, 5 * x ^ 2 - 4 * y ^ 2 - z ^ 2 = n := by

  have eq1 : 3 * y * z + x * z = 2 * x * y := by
    field_simp [hx, hy, hz] at h2 ⊢
    nlinarith

  rw [show z = 3 * x + 2 * y by linarith [h1]] at eq1
  have eq2 : 3 * x ^ 2 + 9 * x * y + 6 * y ^ 2 = 0 := by
    nlinarith

  have eq3 : 3 * (x ^ 2 + 3 * x * y + 2 * y ^ 2) = 0 := by
    nlinarith [eq2]

  have eq4 : x ^ 2 + 3 * x * y + 2 * y ^ 2 = 0 := by
    linarith

  have eq5 : (x + y) * (x + 2 * y) = 0 := by
    nlinarith [eq4]

  cases' (mul_eq_zero.mp eq5) with h3 h4
  · -- Assume x + y = 0, so x = -y
    have hx1 : x = -y := by
      linarith
    have hz1 : z = -y := by
      nlinarith [h1, hx1]
    have h6 : 5 * x ^ 2 - 4 * y ^ 2 - z ^ 2 = (0 : ℝ) := by
      rw [hx1]
      rw [hz1]
      nlinarith
    refine' ⟨0, by
      norm_num at h6 ⊢
      all_goals 
        linarith
    ⟩

  · -- Assume x + 2 * y = 0
    have hx2 : x = -2 * y := by 
      linarith
    have hz2 : z = -4 * y := by
      nlinarith [h1, hx2]
    have h7 : 5 * x ^ 2 - 4 * y ^ 2 - z ^ 2 = (0 : ℝ) := by
      rw [hx2]
      rw [hz2]
      nlinarith
    refine' ⟨0, by 
      norm_num at h7 ⊢
      all_goals 
        linarith 
    ⟩