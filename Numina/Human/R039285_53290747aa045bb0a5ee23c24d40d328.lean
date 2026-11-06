import Mathlib

/- What is the smallest positive integer $x$ that, when multiplied by $400$, produces a product that is a multiple of $576$? -/
theorem algebra_17104 : IsLeast {x | 0 < x ∧ 576 ∣ 400 * x} 36 := by
  exact ⟨by decide, fun b ⟨hb₁, _⟩ => by omega⟩