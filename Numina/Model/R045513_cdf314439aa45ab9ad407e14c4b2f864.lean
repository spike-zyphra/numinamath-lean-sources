import Mathlib

theorem algebra_290141 : {k : ℝ | ∃ x y : ℝ, (x^2 + 6 * x + 12) * (5 * y^2 + 2 * y + 1) = 12 / 5 ∧ x * y = k} = {3 / 5} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward: if ∃ x y satisfying the equation, then k = 3/5
    rintro ⟨x, y, h_eq, hxy⟩
    have h1 : x ^ 2 + 6 * x + 12 ≥ 3 := by
      nlinarith [sq_nonneg (x + 3)]
    have h2 : 5 * y^2 + 2 * y + 1 ≥ 4 / 5 := by
      nlinarith [sq_nonneg (y + 1 / 5)]
    -- Now prove that the equality constraints force x and y to their unique values
    have h3 : (x + 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y + 1 / 5), h_eq]
    have h4 : x + 3 = 0 := by
      nlinarith
    have hx : x = -3 := by
      nlinarith
    -- Now using h_eq to solve for y
    have h5 : (y + 1 / 5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y + 1 / 5), h_eq]
    have h6 : y + 1 / 5 = 0 := by
      nlinarith
    have hy : y = -1 / 5 := by
      nlinarith
    rw [show k = x * y by linarith [hxy]]
    rw [hx, hy]
    norm_num
  · -- Backward: if k = 3/5, then ∃ x y satisfying the equation.
    intro hk
    rw [hk] at *
    use -3
    use -1 / 5
    constructor
    · -- Check the equation
      norm_num
    · -- Check the product
      norm_num