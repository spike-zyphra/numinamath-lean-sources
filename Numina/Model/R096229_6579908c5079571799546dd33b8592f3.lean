import Mathlib

theorem inequalities_297552 :
    IsLeast {x | ∃ a b c : ℝ, x = a * b + b * c + c * a ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3} (-3 / 2) := by
  constructor
  · -- Show that -3/2 can indeed be achieved with a specific combination of a, b, c.
    use -1 / Real.sqrt 2, -1 / Real.sqrt 2, 2 / Real.sqrt 2
    constructor
    · -- Verify that with these values of a, b, c, the value of xy + yz + zx is indeed -3/2.
      field_simp
      <;> ring_nf <;> norm_num
    · -- Verify that with these values of a, b, c, the constraint x² + y² + z² = 3 holds true.
      field_simp
      <;> ring_nf <;> norm_num
  · -- Now prove that -3/2 is indeed the least possible value.
    intro x hx
    rcases hx with ⟨a, b, c, heq1, heq2⟩
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]