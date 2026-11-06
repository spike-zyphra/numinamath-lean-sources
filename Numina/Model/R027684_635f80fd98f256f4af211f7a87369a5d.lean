import Mathlib

theorem calculus_22520 (k : ℝ) :
    ∃ v : ℝ × ℝ × ℝ, v ≠ 0 ∧
      (2 * v.1 - 2 * v.2.1 + v.2.2 = k * v.1 ∧
       2 * v.1 - 3 * v.2.1 + 2 * v.2.2 = k * v.2.1 ∧
       -1 * v.1 + 2 * v.2.1 + 0 * v.2.2 = k * v.2.2) ↔ k = 1 ∨ k = -3 := by
  by_cases h : k = 1
  · -- k = 1
    use (1, 1, 1)
    simp [h]
    <;> norm_num
    <;> tauto
  · -- k ≠ 1
    by_cases h' : k = -3
    · -- k = -3
      use (1, 2, -1)
      simp [h']
      <;> norm_num
      <;> tauto
    · -- k ≠ 1 and k ≠ -3
      use (0, 0, 0)
      simp at *
      <;> try { tauto }