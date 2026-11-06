import Mathlib

theorem algebra_161760 :
  {(x, y) : ℝ × ℝ | x + y = 3 ∧ x^5 + y^5 = 33} = {(1, 2), (2, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfy x + y = 3 and x^5 + y^5 = 33, prove (x, y) ∈ {(1, 2), (2, 1)}
    rintro ⟨h1, h2⟩
    have h3 : y = 3 - x := by linarith
    rw [h3] at h2
    have h4 : (x - 1) * (x - 2) = 0 := by 
      ring_nf at h2 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x - 2)), sq_nonneg ((x - 1.5) * (x - 1.5)), sq_nonneg ((x - 1) * (x - 1)), sq_nonneg ((x - 2) * (x - 2)), sq_nonneg ((x - 2) * (x - 1)), sq_nonneg ((x * (x - 2)) * (x * (x - 2)))]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- x - 1 = 0, so x = 1, y = 2 
      have hx1 : x = 1 := by linarith 
      have hy1 : y = 2 := by 
        linarith [h1, hx1]
      left 
      simp [hx1, hy1]
    · -- x - 2 = 0, so x = 2, y = 1 
      have hx2 : x = 2 := by linarith 
      have hy2 : y = 1 := by 
        linarith [h1, hx2]
      right 
      simp [hx2, hy2]
  · -- Show that (1, 2) and (2, 1) satisfy the system.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (1, 2)
      constructor
      · norm_num 
      · norm_num 
    · -- Check (2, 1)
      constructor
      · norm_num 
      · norm_num