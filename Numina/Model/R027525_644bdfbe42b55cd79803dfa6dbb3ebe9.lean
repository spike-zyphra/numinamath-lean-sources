import Mathlib

theorem algebra_237973 {a b c : ℝ} (ha : a ≠ 0) (h : 2016 + a^2 + a * c < a * b) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ a * x1^2 + b * x1 + c = 0 ∧ a * x2^2 + b * x2 + c = 0 := by
  have h1 : b ^ 2 - 4 * a * c > 0 := by
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_nonneg (b - 2 * a), sq_nonneg (b - (a + c)), sq_nonneg (a - b), sq_nonneg (a + c - b), sq_nonneg (b - a), sq_nonneg (b + a), sq_nonneg (c - b), sq_nonneg (a * 4)]
  use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a), (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
  constructor
  · -- Show that the two roots are distinct.
    have h3 : Real.sqrt (b ^ 2 - 4 * a * c) > 0 := by
      have h2_pos : b ^ 2 - 4 * a * c > 0 := h1
      have h2_pos2 : Real.sqrt (b ^ 2 - 4 * a * c) > 0 := by
        apply Real.sqrt_pos.2
        linarith
      linarith
    by_contra h_eq
    have eq6 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
      exact_mod_cast h_eq
    have eq7 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) := by
      have h4 : (2 * a) ≠ 0 := by
        intro h5
        apply ha
        linarith
      field_simp [h4] at eq6 ⊢
      <;> nlinarith
    have eq8 : Real.sqrt (b ^ 2 - 4 * a * c) = 0 := by
      nlinarith
    linarith [show Real.sqrt (b ^ 2 - 4 * a * c) > 0 by linarith [h3, eq8]]
  constructor
  · -- Show that the first root is a solution.
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
    <;> nlinarith
  · -- Show that the second root is a solution.
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
    <;> nlinarith