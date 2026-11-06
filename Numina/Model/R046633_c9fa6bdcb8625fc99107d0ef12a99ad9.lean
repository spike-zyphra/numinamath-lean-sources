import Mathlib

theorem algebra_6272 (f : ℝ → ℝ) :
    (∀ x, f x + x * f (1 - x) = x) ↔
    ∀ x, f x = x ^ 2 / (x ^ 2 - x + 1) := by
  constructor
  · -- Assume that ∀ x, f x + x * f (1 - x) = x, prove ∀ x, f x = x ^ 2 / (x ^ 2 - x + 1)
    intro h
    intro x
    have eq1 := h x
    have eq2 := h (1 - x)
    have eq3 : f (1 - x) + (1 - x) * f x = 1 - x := by
      have h1 := h (1 - x)
      have h2 : 1 - (1 - x) = x := by
        ring
      simp [h2] at h1 ⊢
      linarith
    have eq4 : f (1 - x) = 1 - x - (1 - x) * f x := by
      linarith [eq3]
    rw [eq4] at eq1
    have eq5 : f x * (x ^ 2 - x + 1) = x ^ 2 := by
      ring_nf at eq1 ⊢
      linarith
    have hx2 : f x = x ^ 2 / (x ^ 2 - x + 1) := by
      have h1 : f x * (x ^ 2 - x + 1) = x ^ 2 := eq5
      have h2 : x ^ 2 - x + 1 ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2)]
      field_simp at h1 ⊢
      linarith
    exact hx2
  · -- Assume that ∀ x, f x = x ^ 2 / (x ^ 2 - x + 1), prove the functional equation
    intro h x
    have eq1 := h x
    have eq2 := h (1 - x)
    simp [eq1, eq2]
    field_simp [(show x ^ 2 - x + 1 ≠ 0 by
      nlinarith [sq_nonneg (x - 1 / 2)]
    ), (show (1 - x) ^ 2 - (1 - x) + 1 ≠ 0 by
      nlinarith [sq_nonneg ( (1 - x) - 1 / 2)]
    )
    ]
    <;> ring_nf <;> nlinarith