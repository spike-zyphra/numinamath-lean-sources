import Mathlib

theorem algebra_290742 :
  {(x, y) : ℝ × ℝ | x^2 + 3 * x * y = 18 ∧ x * y + 3 * y^2 = 6} = {(3, 1), (-3, -1)} := by
  ext ⟨x, y⟩ 
  simp 
  constructor 
  · -- Assume h1 x^2 + 3xy = 18 and h2 xy + 3y^2 = 6 prove {(3,1), (-3,-1)}
    rintro ⟨h1, h2⟩
    have h3 : x * y = 3 := by
      nlinarith [sq_nonneg (x + 3 * y), sq_nonneg (x - y), sq_nonneg (x + 3), sq_nonneg (y + 1)]
    -- We now have both equations and the fact that x * Y = 3.
    have h4 : 3 * y ^ 2 = 3 := by 
      nlinarith [h2, h3]
    -- From 3 * y^2 = 3, we can derive y^2 = 1
    have h5 : y ^ 2 = 1 := by
      linarith
    -- From y^2 = 1, we have y = 1 or y = -1
    have h6 : y = 1 ∨ y = -1 := by 
      rw [sq_eq_one_iff] at h5 
      tauto 
    cases h6 with
    | inl hy1 =>
      have hx1 : x = 3 := by
        rw [hy1] at h3 
        linarith 
      left
      simp [hx1, hy1] 
    | inr hy2 =>
      have hx2 : x = -3 := by
        rw [hy2] at h3 
        linarith 
      right 
      simp [hx2, hy2] 
  · -- Show that (3, 1) and (-3, -1) satisfy both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check both equations for (3, 1)
      constructor
      · norm_num 
      · norm_num 
    · -- Check both equations for (-3, -1)
      constructor 
      · norm_num 
      · norm_num