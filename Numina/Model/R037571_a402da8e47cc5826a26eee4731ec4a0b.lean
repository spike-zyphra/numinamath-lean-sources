import Mathlib

theorem algebra_287046_set_eq {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
  {(x, y, z) : ℝ × ℝ × ℝ | a^3 + a^2 * x + a * y + z = 0 ∧ 
                          b^3 + b^2 * x + b * y + z = 0 ∧ 
                          c^3 + c^2 * x + c * y + z = 0} =
  {(-(a + b + c), a*b + a*c + b*c, -a*b*c)} := by

  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume the equations hold, prove the solution
    rintro ⟨h₁, h₂, h₃⟩
    have eq1 : (b - a) * (b^2 + a * b + a^2) + (b - a) * (x * (b + a)) + (b - a) * y = 0 := by
      nlinarith
    have eq1' : b^2 + a * b + a^2 + x * (b + a) + y = 0 := by
      apply (mul_left_inj' (sub_ne_zero.mpr hab)).mp 
      linarith

    have eq2 : (c - b) * (c^2 + b * c + b^2) + (c - b) * (x * (c + b)) + (c - b) * y = 0 := by
      nlinarith
    have eq2' : c^2 + b * c + b^2 + x * (c + b) + y = 0 := by
      apply (mul_left_inj' (sub_ne_zero.mpr hbc)).mp
      linarith
    have eq3 : (c - a) * (c + a + b + x) = 0 := by
      nlinarith
    have hx1 : x = -(a + b + c) := by
      apply (mul_left_inj' (sub_ne_zero.mpr hca)).mp 
      linarith

    have hy1 : y = a * b + a * c + b * c := by
      rw [hx1] at eq1'
      nlinarith
    have hz1 : z = -a * b * c := by
      rw [hx1, hy1] at h₁
      nlinarith
    simp [hx1, hy1, hz1]

  · -- Assume the solution, prove the equations
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Check first equation
      ring
    constructor
    · -- Check second equation
      ring
    · -- Check third equation
      ring