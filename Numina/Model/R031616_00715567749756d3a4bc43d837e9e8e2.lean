import Mathlib

theorem algebra_163358 : 
    { (x, y, z) : ℝ × ℝ × ℝ | x + y - z = 4 ∧ x^2 + y^2 - z^2 = 12 ∧ x^3 + y^3 - z^3 = 34 } 
    = 
    ({(2, 3, 1), (3, 2, 1)} : Set (ℝ × ℝ × ℝ)) := by 
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) satisfies the system
    rintro ⟨h₁, h₂, h₃⟩
    have hz : z = x + y - 4 := by 
      linarith
    rw [hz] at h₂ h₃
    have eq1 : x * y = 4 * x + 4 * y - 14 := by
      nlinarith 
    have eq2 : (x - 2) * (x - 3) = 0 := by 
      ring_nf at h₂ h₃
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (y - 3)]
    cases' (mul_eq_zero.mp eq2) with h5 h6
    · -- Case x - 2 = 0, so x = 2
      have hx2 : x = (2 : ℝ) := by linarith 
      have hy3 : y = (3 : ℝ) := by 
        rw [hx2] at eq1
        linarith 
      have hz1 : z = (1 : ℝ) := by 
        rw [hx2, hy3] at hz
        linarith 
      simp [hx2, hy3, hz1]
    · -- Case x - 3 = 0, so x = 3
      have hx3 : x = (3 : ℝ) := by linarith 
      have hy2 : y = (2 : ℝ) := by 
        rw [hx3] at eq1
        linarith 
      have hz1 : z = (1 : ℝ) := by 
        rw [hx3, hy2] at hz
        linarith 
      simp [hx3, hy2, hz1]
  · -- Show that (2,3,1) and (3,2,1) satisfy the system
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- First solution (2,3,1)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Second solution (3,2,1)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num