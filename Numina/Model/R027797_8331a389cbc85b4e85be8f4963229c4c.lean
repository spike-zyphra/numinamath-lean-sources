import Mathlib

theorem algebra_10752 (m b : ℝ) (h₀ : b = 5) (h₁ : ∃ x y, 9*x^2+16*y^2=144 ∧ y=m*x+b) :
    m ≤ -1 ∨ m ≥ 1 := by
  rcases h₁ with ⟨x, y, h2, h3⟩
  rw [h₀] at h3
  have h4 : 9 * x ^ 2 + 16 * (m * x + 5) ^ 2 = 144 := by
    have h5 : y = m * x + 5 := by linarith
    rw [h5] at h2
    linarith
  have h5 : (9 + 16 * m ^ 2) * x ^ 2 + 160 * m * x + 256 = 0 := by
    nlinarith
  have h6 : (160 * m) ^ 2 - 4 * (9 + 16 * m ^ 2) * 256 ≥ 0 := by 
    nlinarith [sq_nonneg ((9 + 16 * m ^ 2) * x + 80 * m), sq_nonneg (x * (9 + 16 * m^2) + 80 * m), sq_nonneg (m), sq_nonneg (x - (-160 * m) / (2 * (9 + 16 * m^2)))]
  have h7 : 9216 * (m ^ 2 - 1) ≥ 0 := by
    nlinarith
  have h8 : m ^ 2 - 1 ≥ 0 := by
    nlinarith
  by_contra h
  push_neg at h
  nlinarith [sq_nonneg (m - 1), sq_nonneg (m + 1)]