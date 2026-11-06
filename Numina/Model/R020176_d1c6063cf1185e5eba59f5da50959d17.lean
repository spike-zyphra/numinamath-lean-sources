import Mathlib

theorem algebra_311337 {a b c : ℝ} (ha : a ≠ 0) (hroots : ∃ x1 x2 : ℝ, x1 ≠ 0 ∧ x2 ≠ 0 ∧ a * x1^2 + b * x1 + c = 0 ∧ a * x2^2 + b * x2 + c = 0) :
    ∃ x1 x2 : ℝ, x1 ≠ 0 ∧ x2 ≠ 0 ∧ c^2 * x1^2 - (b^2 - 2 * a * c) * x1 + a^2 = 0 ∧ c^2 * x2^2 - (b^2 - 2 * a * c) * x2 + a^2 = 0 := by
  rcases hroots with ⟨x1, x2, hx1, hx2, h1, h2⟩
  use 1 / x1 ^ 2, 1 / x2 ^ 2
  constructor
  · -- Show the first root is non-zero
    by_contra h
    have : 1 / x1 ^ 2 = 0 := by simpa using h
    field_simp [hx1] at this
    <;> try { nlinarith [this] }
  constructor
  · -- Show the second root is non-zero
    by_contra h
    have : 1 / x2 ^ 2 = 0 := by simpa using h
    field_simp [hx2] at this
    <;> try { nlinarith [this] }
  constructor
  · -- Show the first root satisfies the quadratic equation
    have h11 : a * x1 ^ 2 + b * x1 + c = 0 := h1
    have h12 : c = -a * x1^2 - b * x1 := by linarith 
    rw [h12]
    field_simp [hx1]
    <;> nlinarith [sq_pos_of_ne_zero hx1, sq_nonneg (x1 * a), sq_nonneg (x1 * b), sq_nonneg ((-a * x1 ^ 2 - b * x1)), sq_pos_of_ne_zero ha]
  · -- Show the second root satisfies the quadratic equation
    have h21 : a * x2 ^ 2 + b * x2 + c = 0 := h2
    have h12 : c = -a * x2^2 - b * x2 := by linarith 
    rw [h12]
    field_simp [hx2]
    <;> nlinarith [sq_pos_of_ne_zero hx2, sq_nonneg (x2 * a), sq_nonneg (x2 * b), sq_nonneg ((-a * x2 ^ 2 - b * x2)), sq_pos_of_ne_zero ha]