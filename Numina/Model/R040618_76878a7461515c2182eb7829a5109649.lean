import Mathlib

theorem algebra_140433 :
    {(x, y, z) : ℝ × ℝ × ℝ | 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 3 * x * y ∧ x^2 + y^2 + z^2 = 3 * x * z ∧ x^3 + y^3 + z^3 = 3 * y * z} = {(0, 0, 0), (1, 1, 1)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Forward direction: if $(x, y, z)$ satisfies the conditions, then it's in {(0,0,0), (1,1,1)}
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    have eq1 : y = x := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
    have eq2 : z = x := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
    -- Now we also need to prove that from above equations and h1, h2, h3 derive substitutions
    rw [show y = x by linarith [eq1]] at h1 h2 h3
    rw [show z = x by linarith [eq2]] at h1 h2 h3
    have eq3 : (x * (x - 1)) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp eq3) with 
    | inl h8 =>
      have hx0 : x = 0 := by
        linarith
      have hy0 : y = 0 := by 
        nlinarith [eq1, hx0]
      have hz0 : z = 0 := by 
        nlinarith [eq2, hx0]
      simp [hx0, hy0, hz0]
    | inr h8 =>
      have hx1 : x = 1 := by linarith
      have hy1 : y = 1 := by 
        nlinarith [eq1, hx1]
      have hz1 : z = 1 := by 
        nlinarith [eq2, hx1]
      simp [hx1, hy1, hz1]
  · -- Reverse direction: if (x,y,z) is in {(0,0,0), (1,1,1)}, then it satisfies the conditions
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · constructor
      · norm_num -- 0 ≤ (0 : ℝ)
      constructor
      · norm_num -- 0 ≤ (0 : ℝ)
      constructor
      · norm_num -- 0 ≤ (0 : ℝ)
      constructor
      · norm_num -- 0 + 0 + 0 = 3 * 0 * 0
      constructor
      · norm_num -- 0^2 + 0^2 + 0^2 = 3 * 0 * 0
      · norm_num -- 0^3 + 0^3 + 0^3 = 3 * 0 * 0
    · constructor
      · norm_num -- 0 ≤ (1 : ℝ)
      constructor
      · norm_num -- 0 ≤ (1 : ℝ)
      constructor
      · norm_num -- 0 ≤ (1 : ℝ)
      constructor
      · norm_num -- 1 + 1 + 1 = 3 * 1 * 1
      constructor
      · norm_num -- 1^2 + 1^2 + 1^2 = 3 * 1 * 1
      · norm_num -- 1^3 + 1^3 + 1^3 = 3 * 1 * 1