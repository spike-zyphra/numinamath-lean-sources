import Mathlib

open Real Set

theorem algebra_324186 : IsLeast {z : ℝ | ∃ x y, z = cos (x + y) + 2 * cos x + 2 * cos y} (-3) := by 
  constructor 
  · -- Show that -3 is in the set 
    use Real.pi, Real.pi 
    have h1 : cos (Real.pi + Real.pi) = 1 := by 
      have h2 : Real.pi + Real.pi = 2 * Real.pi := by ring
      rw [h2] 
      exact cos_two_pi 
    have h2 : cos (Real.pi) = -1 := by 
      exact cos_pi 
    rw [h1] 
    rw [h2] 
    norm_num 
  · -- Show that -3 is the least element in the set 
    intro z h 
    rcases h with ⟨x, y, hz⟩ 
    have h3 : cos (x + y) = cos x * cos y - sin x * sin y := by 
      rw [cos_add] 
    rw [h3] at hz 
    have h4 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x 
    have h5 : cos y ^ 2 + sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y 
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos y + 1), 
      sq_nonneg (sin x), sq_nonneg (sin y), 
      sq_nonneg (cos x - (-1)), sq_nonneg (cos y - (-1)), 
      Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, 
      sq_nonneg (cos x - cos y), 
      sq_nonneg (sin x - sin y)
    ]