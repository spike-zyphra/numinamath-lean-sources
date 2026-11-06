import Mathlib
theorem algebra_604671 : {(x, y, z) : ℝ × ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x + y + z = 2008 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 6024 ^ 2 ∧ 1 / x + 1 / y + 1 / z = 1 / 2008} = {(2008, 4016, -4016), (2008, -4016, 4016), (4016, 2008, -4016), (4016, -4016, 2008), (-4016, 2008, 4016), (-4016, 4016, 2008)}:= by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Forward implication: the equations imply the solutions
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    -- Simplify the reciprocal equation by multiplying through by xyz
    have h4 : x * y + x * z + y * z = x * y * z / 2008:= by
      field_simp at h3
      field_simp
      nlinarith
    -- Calculate the expansion of (x + y + z)^2 using the sum of squares formula
    have h5 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + x * z + y * z):= by
      ring
    rw [h1, h2] at h5
    -- Substitute the known value of xy + yz + zx and solve
    rw [h4] at h5
    -- Derive that xyz = -4096
    have eq1 : x * y * z = -4 * 2008 ^ 3 := by
      nlinarith
    -- Use conventions to simplify our problem
    have h7 : (x - 2008) * (y - 2008) * (z - 2008) = 0 := by
      nlinarith [sq_nonneg (x + y + z - 2008), sq_nonneg (x * y + x * z + y * z + 4 * 2008 ^ 2), sq_nonneg (x * y * z + 4 * 2008 ^ 3)]
    cases' (mul_eq_zero.mp h7) with h8 h9
    cases' (mul_eq_zero.mp h8) with h10 h11
    · -- Case x = 2008
      have hx1 : x = 2008 := by linarith
      simp [hx1] at h1 h4 eq1
      have hsq : (y - 4016) * (y + 4016) = 0 := by
        nlinarith [sq_nonneg (y + z), sq_nonneg (y - z)]
      cases' (mul_eq_zero.mp hsq) with hy1 hy2
      · -- Case y = 4016
        have hy1' : y = 4016 := by nlinarith
        have hz1' : z = -4016 := by linarith [h1, hy1']
        simp [hx1, hy1', hz1']
      · -- Case y = -4016
        have hy2' : y = -4016 := by nlinarith
        have hz2' : z = 4016 := by linarith [h1, hy2']
        simp [hx1, hy2', hz2']
    · -- Case y = 2008
      have hy1 : y = 2008 := by linarith
      simp [hy1] at h1 h4 eq1
      have hsq : (x - 4016) * (x + 4016) = 0 := by
        nlinarith [sq_nonneg (x + z), sq_nonneg (x - z)]
      cases' (mul_eq_zero.mp hsq) with hx3 hx4
      · -- Case x = 4016
        have hx3' : x = 4016 := by nlinarith
        have hz3' : z = -4016 := by linarith [h1, hx3']
        simp [hx3', hy1, hz3']
      · -- Case x = -4016
        have hx4' : x = -4016 := by nlinarith
        have hz4' : z = 4016 := by linarith [h1, hx4']
        simp [hx4', hy1, hz4']
    · -- Case z = 2008
      have hz1 : z = 2008 := by linarith
      simp [hz1] at h1 h4 eq1
      have hsq : (x - 4016) * (x + 4016) = 0 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
      cases' (mul_eq_zero.mp hsq) with hx5 hx6
      · -- Case x = 4016
        have hx5' : x = 4016 := by nlinarith
        have hy5' : y = -4016 := by linarith [h1, hx5']
        simp [hx5', hz1, hy5']
      · -- Case x = -4016
        have hx6' : x = -4016 := by nlinarith
        have hy6' : y = 4016 := by linarith [h1, hx6']
        simp [hx6', hz1, hy6']
  · -- Backward implication: each solution satisfies the equations
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals
        norm_num
        <;> linarith