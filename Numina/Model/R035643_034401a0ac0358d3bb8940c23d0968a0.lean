import Mathlib

theorem algebra_231374 :
    {(x, y, z) : ℝ × ℝ × ℝ | ∃ a b c : ℝ,
    a * x + b * y - c * z = 2 * a * b ∧
    a * x - b * y + c * z = 2 * a * c ∧
    -(a * x) + b * y - c * z = 2 * b * c} = 
    {(x, y, z) : ℝ × ℝ × ℝ | ∃ a b c : ℝ,
    x = b + c ∧ y = a + c ∧ z = a + b} := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq]
  constructor
  · -- First direction: prove the implication from the equations to the existential quantifier
    rintro ⟨a, b, c, h1, h2, h3⟩
    use (y + z - x) / 2, (x + z - y) / 2, (x + y - z) / 2
    constructor
    · -- Show that x = b' + c'
      ring
    constructor
    · -- Show that y = a' + c'
      ring
    · -- Show that z = a' + b'
      ring
  · -- Second direction: prove the converse implication
    rintro ⟨a, b, c, hx, hy, hz⟩
    refine' ⟨0, 0, 0, ?_, ?_, ?_⟩
    all_goals
      simp [hx, hy, hz]
      <;> norm_num
      all_goals linarith