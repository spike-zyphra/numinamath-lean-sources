import Mathlib

theorem algebra_127533 {a b c : ℝ} (h₀ : a * b * c ≠ 0) (h₁ : a + b + c = 2)
    (h₂ : a^2 + b^2 + c^2 = 2) :
    (1 - a)^2 / (b * c) + (1 - b)^2 / (c * a) + (1 - c)^2 / (a * b) = 3 := by
  -- First, we establish that none of a, b, c is zero
  have h₃ : a ≠ 0 := by
    by_contra h
    have h₄ : a * b * c = 0 := by
      simp [h]
    contradiction
  have h₄ : b ≠ 0 := by
    by_contra h
    have h₅ : a * b * c = 0 := by
      simp [h]
    contradiction
  have h₅ : c ≠ 0 := by
    by_contra h
    have h₆ : a * b * c = 0 := by
      simp [h]
    contradiction
  have h₆ : a * b + b * c + c * a = 1 := by
    have h₇ : a^2 + b^2 + c^2 = (a + b + c)^2 - 2 * (a * b + b * c + c * a) := by ring
    rw [h₁] at h₇
    linarith [h₂, h₇]
  -- Convert the expression to numerator multiplied by $abc$ to clear denominators
  have eq1 : (1 - a)^2 / (b * c) + (1 - b)^2 / (c * a) + (1 - c)^2 / (a * b) =
    (a * (1 - a)^2 + b * (1 - b)^2 + c * (1 - c)^2) / (a * b * c) := by
    field_simp [h₄, h₃, h₅, h₀]
    ring
  rw [eq1]
  have eq2 : a * (1 - a)^2 + b * (1 - b)^2 + c * (1 - c)^2 = 3 * (a * b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          h₁, h₆, 
          sq_nonneg (a + b + c - 2), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)
         ]
  rw [eq2]
  field_simp [h₀]
  <;> ring