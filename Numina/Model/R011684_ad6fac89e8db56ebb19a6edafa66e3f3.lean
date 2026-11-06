import Mathlib

theorem algebra_159246 :
    {(x, y, z) : ℝ × ℝ × ℝ | x * y = z * (x + y + z) ∧ y * z = 4 * x * (x + y + z) ∧ z * x = 9 * y * (x + y + z)} = {(-3 * t, -2 * t, 6 * t) | t : ℝ} := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x,y,z) satisfies the three equations.
    rintro ⟨h₁, h₂, h₃⟩
    have eq1 : z ^ 2 = 4 * x ^ 2 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    have hz : z = 2 * x ∨ z = -2 * x := by
      have h : z ^ 2 - 4 * x ^ 2 = 0 := by linarith
      have h' : (z - 2 * x) * (z + 2 * x) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h') with h4 h5
      · -- z - 2x = 0
        left 
        linarith 
      · -- z + 2x = 0
        right
        linarith 
    cases hz with
    | inl h_z2x => 
      have eq2 : y = -6 * x := by
        nlinarith [h₂, h_z2x, sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      have eq3 : x = 0 := by
        nlinarith [h₃, h_z2x, eq2, sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      have eq4 : y = 0 := by
        nlinarith [eq3, eq2]
      have eq5 : z = 0 := by
        nlinarith [eq3, h_z2x]
      use 0 
      constructor
      · -- Show x = -3t
        linarith 
      constructor
      · -- Show y = -2t
        linarith 
      · -- Show z = 6t
        linarith 
    | inr h_z2x => 
      have eq2 : y = (2/3) * x := by
        nlinarith [h₂, h_z2x, sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
      use x / (-3)
      constructor
      · -- Show x = -3t
        field_simp
      constructor
      · -- Show y = -2t
        rw [eq2]
        field_simp 
      · -- Show z = 6t
        nlinarith [h_z2x]
  · -- Assume (x,y,z) is of the form (-3t, -2t, 6t).
    rintro ⟨t, rfl, rfl, rfl⟩
    constructor 
    · -- Show h1.
      ring 
    constructor 
    · -- Show h2.
      ring 
    · -- Show h3.
      ring