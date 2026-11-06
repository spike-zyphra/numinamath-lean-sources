import Mathlib

theorem calculus_18703 (k : ℝ) :
    ∃ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x + k * y - z = 0 ∧ k * x - y - z = 0 ∧ x + y - k * z = 0 ↔
    k = -1 ∨ k = 0 ∨ k = 1 := by
  by_cases h1 : k = -1
  · -- If k = -1, use the solution (0, 1, -1)
    use 0, 1, -1
    simp [h1]
    <;> norm_num
    <;> tauto
  · -- If k ≠ -1, check if k = 0
    by_cases h2 : k = 0
    · -- If k = 0, use the solution (1, -1, 1)
      use 1, -1, 1
      simp [h2]
      <;> norm_num
      <;> tauto
    · -- If k ≠ -1 and k ≠ 0, check if k = 1
      by_cases h3 : k = 1
      · -- If k = 1, use the solution (1, 0, 1)
        use 1, 0, 1
        simp [h3]
        <;> norm_num
        <;> tauto
      · -- If k ≠ -1, 0, 1, then the only solution is trivial
        use 0, 0, 0
        simp [h1, h2, h3]
        <;> norm_num
        <;> tauto