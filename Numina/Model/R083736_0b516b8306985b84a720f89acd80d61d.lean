import Mathlib

theorem algebra_1595 (a : ℝ) (x₁ x₂ : ℝ)
    (h : {x : ℝ | 3 * (x + 4) = 2 * a + 5} = {x₁})
    (h' : {x : ℝ | ((4 * a + 1) * x) / 4 = (a * (3 * x - 4)) / 3} = {x₂}) :
    x₁ > x₂ → a > 7 / 18 := by
  intro h1
  have h1' : 3 * (x₁ + 4) = 2 * a + 5 := by
    have h_eq : x₁ ∈ {x : ℝ | 3 * (x + 4) = 2 * a + 5} := by
      rw [h]
      simp
    exact h_eq
  have hx1 : x₁ = (2 * a - 7) / 3 := by
    linarith
  have h2' : ((4 * a + 1) * x₂) / 4 = (a * (3 * x₂ - 4)) / 3 := by
    have h_eq : x₂ ∈ {x : ℝ | ((4 * a + 1) * x) / 4 = (a * (3 * x - 4)) / 3} := by
      rw [h']
      simp
    exact h_eq
  have hx2 : x₂ = -16 * a / 3 := by
    linarith
  rw [hx1, hx2] at h1
  linarith