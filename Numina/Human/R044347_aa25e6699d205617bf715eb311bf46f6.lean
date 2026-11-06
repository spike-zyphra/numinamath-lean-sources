import Mathlib

open Real Set

/- Example 8 Solve the functional inequality $f(\sin x) \leqslant \cos 2 x$.

 -/
theorem inequalities_289208 (f : ℝ → ℝ) :
    (∀ x, f (sin x) ≤ cos (2 * x)) ↔ ∀ x ∈ Icc (-1) 1, f x ≤ 1 - 2 * x ^ 2 := by
  -- first we rewrite the cos(2*x) into 1 - 2 (sin x)^2
  simp_rw [cos_two_mul', cos_sq']
  simp_rw [fun x ↦ show 1 - sin x ^ 2 - sin x ^ 2 = 1 - 2 * sin x ^ 2 by ring]
  -- now we'll prove both direction
  constructor <;> rintro h x
  -- left to right, use the hypothesis h on arcsin(x), since x ∈ [-1, 1], sin arcsin cancels out
  . rintro ⟨hx₁, hx₂⟩
    have := h (arcsin x)
    rwa [sin_arcsin hx₁ hx₂] at this
  -- right to left, use hypothesis on sin x, as -1 ≤ sin x ≤ 1
  . exact h (sin x) ⟨neg_one_le_sin x, sin_le_one x⟩