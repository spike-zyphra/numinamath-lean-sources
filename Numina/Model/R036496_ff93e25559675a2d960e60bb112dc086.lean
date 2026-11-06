import Mathlib

theorem algebra_167621 :
    {(x, y) : ℝ × ℝ | 3*x^2+2*y^2+2*x+3*y=0 ∧ 4*x^2-3*y^2-3*x+4*y=0} = 
    {(0, 0), (-1, -1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume they satisfy both equations
    rintro ⟨h1, h2⟩
    have h3 : x^2 + y = 0 := by
      nlinarith
    have h4 : y = -x^2 := by linarith
    rw [h4] at h1
    have h5 : 2 * x^4 + 2 * x = 0 := by
      nlinarith
    have h6 : 2 * x * (x^3 + 1) = 0 := by
      ring_nf at h5 ⊢
      linarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- 2 * x = 0
      have hx : x = 0 := by linarith
      have hy : y = 0 := by
        rw [hx] at h4
        nlinarith
      left
      simp [hx, hy]
    · -- x^3 + 1 = 0
      have hx : x = -1 := by
        have hx3 : x^3 = -1 := by linarith
        have hx4 : x^3 + 1 = 0 := by linarith
        have hx5 : (x + 1) * (x^2 - x + 1) = 0 := by
          ring_nf at hx4 ⊢
          nlinarith
        cases' (mul_eq_zero.mp hx5) with hx6 hx7
        · -- x + 1 = 0
          linarith
        · -- x^2 - x + 1 = 0
          -- The quadratic x^2 - x + 1 has no real roots since discriminant is negative.
          have h8 : x^2 - x + 1 > 0 := by
            nlinarith [sq_nonneg (x - 1 / 2)]
          nlinarith
      have hy : y = -1 := by
        rw [hx] at h4
        nlinarith
      right
      simp [hx, hy]
  · -- Show that both equations are satisfied
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (0, 0)
      constructor
      · -- Check first equation
        norm_num
      · -- Check second equation
        norm_num
    · -- (-1, -1)
      constructor
      · -- Check first equation
        norm_num
      · -- Check second equation
        norm_num