import Mathlib

theorem algebra_198631 (a : ℝ) :
    ∃ x₁ x₂ x₃ x₄ : ℝ,
      x₁ ≥ 0 ∧ x₂ ≥ 0 ∧ x₃ ≥ 0 ∧ x₄ ≥ 0 ∧
      x₁ + x₂ + x₃ + x₄ = 1 ∧
      x₁ + 2 * x₂ + 3 * x₃ + 4 * x₄ = a ∧
      x₁ + 2 ^ 2 * x₂ + 3 ^ 2 * x₃ + 4 ^ 2 * x₄ = a ^ 2 ∧
      x₁ + 2 ^ 3 * x₂ + 3 ^ 3 * x₃ + 4 ^ 3 * x₄ = a ^ 3 ↔
    a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by 

  by_cases h1 : a = 1
  · -- Case 1. Assume a = 1. The variables are (x1 = 1, x2 = 0, x3 = 0, x4 = 0).
    use 1, 0, 0, 0
    simp [h1]
  
  by_cases h2 : a = 2
  · -- Case 2. Assume a = 2. The variables are (x1 = 0, x2 = 1, x3 = 0, x4 = 0).
    use 0, 1, 0, 0
    simp [h2]

  by_cases h3 : a = 3
  · -- Case 3. Assume a = 3. The variables are (x1 = 0, x2 = 0, x3 = 1, x4 = 0).
    use 0, 0, 1, 0
    simp [h3]

  by_cases h4 : a = 4
  · -- Case 4. Assume a = 4. The variables are (x1 = 0, x2 = 0, x3 = 0, x4 = 1).
    use 0, 0, 0, 1
    simp [h4]

  · -- Case 5. Assume a \notin {1, 2, 3, 4}.
    use (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
    simp [h1, h2, h3, h4] at *
    <;> tauto