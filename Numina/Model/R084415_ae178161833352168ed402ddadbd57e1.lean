import Mathlib

theorem algebra_326307 {a b : ℚ} (ha : ∃ x : ℚ, Real.sqrt a = x) (hb : ∃ y : ℚ, Real.sqrt b = y)
    (h : ∃ z : ℚ, Real.sqrt a + Real.sqrt b = z) :
    ∃ x y : ℚ, Real.sqrt a = x ∧ Real.sqrt b = y := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  exact ⟨x, y, ⟨hx, hy⟩⟩