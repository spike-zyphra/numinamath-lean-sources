import Mathlib

theorem algebra_147005 (x y : ℝ) :
    (x^3 + y^3 = 1 ∧ x^4 + y^4 = 1) ↔ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  constructor
  · -- Assume (x^3 + y^3 = 1 ∧ x^4 + y^4 = 1), prove (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
    rintro ⟨h1, h2⟩
    have h3 : x^2 * (x - 1) ^ 2 + y ^ 2 * (y - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x^2 - x), sq_nonneg (y^2 - y), sq_nonneg (x * (x - 1)), sq_nonneg (y * (y - 1)), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1)]
    have h4 : x^2 * (x - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x^2 * (x - 1) ^ 2), sq_nonneg (y ^ 2 * (y - 1) ^ 2), h3, sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have h5 : y ^ 2 * (y - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x^2 * (x - 1) ^ 2), sq_nonneg (y ^ 2 * (y - 1) ^ 2), h3, sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have hx : x = 0 ∨ x = 1 := by
      cases' (mul_eq_zero.1 h4) with h6 h7
      · -- x^2 = 0
        have hx0 : x = 0 := by
          nlinarith
        simp [hx0]
      · -- (x - 1) ^ 2 = 0
        have hx1 : x = 1 := by
          nlinarith
        simp [hx1]
    have hy : y = 0 ∨ y = 1 := by
      cases' (mul_eq_zero.1 h5) with h8 h9
      · -- y^2 = 0
        have hy0 : y = 0 := by
          nlinarith
        simp [hy0]
      · -- (y - 1) ^ 2 = 0
        have hy1 : y = 1 := by
          nlinarith
        simp [hy1]
    cases hx with
    | inl hx0 =>
      cases hy with
      | inl hy0 =>
        exfalso
        nlinarith
      | inr hy1 =>
        left
        constructor
        · linarith
        · linarith
    | inr hx1 =>
      cases hy with
      | inl hy0 =>
        right
        constructor
        · linarith
        · linarith
      | inr hy1 =>
        exfalso
        nlinarith
  · -- Proof of reverse direction
    rintro (h | h)
    · -- (0, 1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- (1, 0)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      · norm_num