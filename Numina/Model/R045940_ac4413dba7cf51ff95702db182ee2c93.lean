import Mathlib

theorem algebra_174120 :
    {(x, y, z) : ℝ × ℝ × ℝ | 2*x+3*y+z=1 ∧ 4*x-y+2*z=2 ∧ 8*x+5*y+3*z=4} = 
    {(1/2, 0, 0)} := by 
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- First, show that if $(x,y,z)$ is a solution, then $(x,y,z) = (1/2, 0, 0)$
    rintro ⟨h1, h2, h3⟩
    
    have hy : y = 0 := by
      linarith
    have h4 : z = 1 - 2 * x := by
      rw [hy] at h1
      linarith
    have hx : x = 1 / 2 := by
      rw [hy] at h3
      rw [h4] at h3
      linarith
    have hz : z = 0 := by
      rw [hx] at h4
      linarith
    simp [hx, hy, hz]
  
  · -- Show that (1/2, 0, 0) is a solution
    rintro ⟨rfl, rfl, rfl⟩
    
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num