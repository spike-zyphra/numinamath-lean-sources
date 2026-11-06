import Mathlib

theorem algebra_314373 (x y z : ℝ) (h₀ : y = 4 * x ^ 3 - 3 * x) (h₁ : z = 4 * y ^ 3 - 3 * y)
    (h₂ : x = 4 * z ^ 3 - 3 * z) :
    ∃ θ, x = Real.cos θ ∧ y = Real.cos (3 * θ) ∧ z = Real.cos (9 * θ) := by
  use (Real.arccos x)
  constructor
  · -- Show that x = Real.cos (Real.arccos x)
    have hx1 : -1 ≤ x := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
    have hx2 : x ≤ 1 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
    rw [Real.cos_arccos]
    all_goals nlinarith
  constructor
  · -- Show that y = Real.cos (3 * (Real.arccos x))
    have h4 : Real.cos (3 * (Real.arccos x)) = 4 * Real.cos (Real.arccos x) ^ 3 - 3 * Real.cos (Real.arccos x) := by
      rw [Real.cos_three_mul]
      <;> ring_nf <;> simp [mul_add, mul_comm, mul_assoc, Real.cos_sq, Real.sin_sq]
      <;> nlinarith [Real.cos_sq_add_sin_sq (Real.arccos x)]
    have h8 : Real.cos (Real.arccos x) = x := by
      have hx1 : -1 ≤ x := by
        nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
      have hx2 : x ≤ 1 := by
        nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
      rw [Real.cos_arccos]
      all_goals nlinarith
    have h5 : Real.cos (3 * (Real.arccos x)) = y := by
      rw [h4, h8]
      all_goals
        nlinarith [h₀, sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    linarith
  · -- Show that z = Real.cos (9 * (Real.arccos x))
    have h4 : Real.cos (9 * (Real.arccos x)) = 4 * Real.cos (3 * (Real.arccos x)) ^ 3 - 3 * Real.cos (3 * (Real.arccos x)) := by
      rw [show 9 * (Real.arccos x) = 3 * (3 * (Real.arccos x)) by ring]
      rw [Real.cos_three_mul]
      <;> ring_nf <;> simp [mul_add, mul_comm, mul_assoc, Real.cos_sq, Real.sin_sq]
      <;> nlinarith [Real.cos_sq_add_sin_sq (3 * (Real.arccos x))]
    have h7 : Real.cos (3 * (Real.arccos x)) = y := by
      have h4 : Real.cos (3 * (Real.arccos x)) = 4 * Real.cos (Real.arccos x) ^ 3 - 3 * Real.cos (Real.arccos x) := by
        rw [Real.cos_three_mul]
        <;> ring_nf <;> simp [mul_add, mul_comm, mul_assoc, Real.cos_sq, Real.sin_sq]
        <;> nlinarith [Real.cos_sq_add_sin_sq (Real.arccos x)]
      have h8 : Real.cos (Real.arccos x) = x := by
        have hx1 : -1 ≤ x := by
          nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
        have hx2 : x ≤ 1 := by
          nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
        rw [Real.cos_arccos]
        all_goals nlinarith
      rw [h4, h8]
      all_goals
        nlinarith [h₀, sq_nonneg (x ^ 2 - 1), sq_nonneg (x), sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    rw [h4, h7]
    all_goals
      nlinarith [h₁, sq_nonneg (y ^ 2 - 1), sq_nonneg (y), sq_nonneg (z ^ 2 - 1), sq_nonneg (z), sq_nonneg (z * x * y - x * y * z), sq_nonneg (y * z * x - z * x * y)]