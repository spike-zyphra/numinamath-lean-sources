import Mathlib

theorem algebra_121575 :
    {(x, y, z) : ℝ × ℝ × ℝ | x - y + z = 2 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 30 ∧ x ^ 3 - y ^ 3 + z ^ 3 = 116} = {(-1, 2, 5), (-1, -5, -2), (-2, 1, 5), (-2, -5, -1), (5, 1, -2), (5, 2, -1)} := by 
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- First direction: if (x, y, z) is in the set, then it's one of the six tuples
    rintro ⟨h1, h2, h3⟩
    have h4 : y = x + z - 2 := by linarith
    rw [h4] at h2 h3
    have h5 : (x + 1) * (x + 2) * (x - 5) = 0 := by
      nlinarith [sq_nonneg (x - z), sq_nonneg (x - 5), sq_nonneg (x + 2), sq_nonneg (z - 5), sq_nonneg (z + 2), sq_nonneg (x - z)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- First case: (x + 1) * (x + 2) = 0
      cases' (mul_eq_zero.mp h6) with h8 h9
      · -- Case x = -1
        have hx : x = -1 := by linarith
        have eq1 : z ^ 2 - 3 * z - 10 = 0 := by
          nlinarith [sq_nonneg (z - 5), sq_nonneg (z + 2)]
        have h12 : (z - 5) * (z + 2) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h12) with
        | inl h13 =>
          have hz : z = 5 := by linarith
          have hy : y = 2 := by
            nlinarith [show y = x + z - 2 by linarith, hx, hz]
          simp [hx, hy, hz]
        | inr h16 =>
          have hz : z = -2 := by linarith
          have hy : y = -5 := by
            nlinarith [show y = x + z - 2 by linarith, hx, hz]
          simp [hx, hy, hz]
      · -- Case x = -2
        have hx : x = -2 := by linarith
        have eq3 : z ^ 2 - 4 * z - 5 = 0 := by
          nlinarith
        have h18 : (z - 5) * (z + 1) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h18) with
        | inl h19 =>
          have hz : z = 5 := by linarith
          have hy : y = 1 := by
            nlinarith [show y = x + z - 2 by linarith, hx, hz]
          simp [hx, hy, hz]
        | inr h20 =>
          have hz : z = -1 := by linarith
          have hy : y = -5 := by
            nlinarith [show y = x + z - 2 by linarith, hx, hz]
          simp [hx, hy, hz]
    · -- Case x = 5
      have hx : x = 5 := by linarith
      have eq3 : z ^ 2 + 3 * z + 2 = 0 := by
        nlinarith [sq_nonneg (z + 1), sq_nonneg (z + 2)]
      have h15 : (z + 1) * (z + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h15) with
      | inl h16 =>
        have hz : z = -1 := by linarith
        have hy : y = 2 := by
          nlinarith [show y = x + z - 2 by linarith, hx, hz]
        simp [hx, hy, hz]
      | inr h17 =>
        have hz : z = -2 := by linarith
        have hy : y = 1 := by
          nlinarith [show y = x + z - 2 by linarith, hx, hz]
        simp [hx, hy, hz]
  · -- Show that each of the six tuples satisfies the three equations
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl
      ⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl
      ⟩)
    · -- (-1, 2, 5)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (-1, -5, -2)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (-2, 1, 5)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (-2, -5, -1)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (5, 1, -2)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (5, 2, -1)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num