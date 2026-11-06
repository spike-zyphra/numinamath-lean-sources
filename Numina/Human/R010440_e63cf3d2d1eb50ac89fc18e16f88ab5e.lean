import Mathlib

/- Find the solution set of the inequality: $-x^2+4x+5<0$. -/
theorem algebra_9014 (x : ℝ) : -x^2 + 4 * x + 5 < 0 ↔ x < -1 ∨ x > 5 := by
  -- rewrite -x^2 + 4 * x + 5 < 0 to (5 - x) * (1 + x) > 0
  have : -x^2 + 4 * x + 5 = (5 - x) * (1 + x) := by
    ring
  -- a*b < 0 iff a > 0 and b < 0 or a < 0 and b > 0
  rw [this, mul_neg_iff]
  -- trivial case analysis
  constructor <;> intro h
  . obtain ⟨_, h⟩ | ⟨h, _⟩ := h
    . exact Or.inl (by linarith)
    . exact Or.inr (by linarith)
  . obtain h | h := h
    . exact Or.inl ⟨by linarith, by linarith⟩
    . exact Or.inr ⟨by linarith, by linarith⟩
