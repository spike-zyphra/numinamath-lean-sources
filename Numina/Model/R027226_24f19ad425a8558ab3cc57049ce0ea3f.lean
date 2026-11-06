import Mathlib

theorem algebra_162041 {f : ℚ → ℚ → ℝ}
    (hpos : ∀ x y, f x y > 0)
    (hf1 : ∀ x y z, f (x * y) z = f x z * f y z)
    (hf2 : ∀ x y z, f z (x * y) = f z x * f z y)
    (hf3 : ∀ x, f x (1 - x) = 1) :
    (∀ x, f x x = 1) ∧ (∀ x, f x (-x) = 1) ∧
    (∀ x y, f x y * f y x = 1) := by
  have h4 : ∀ x z, f x z = 1 := by
    intro x z
    have eq1 := hf1 x 0 z
    have hxz0 : (x * (0 : ℚ)) = (0 : ℚ) := by ring
    simp [hxz0] at eq1
    have hx0 : f 0 z > 0 := hpos 0 z
    have hx1 : f x z = 1 := by
      nlinarith
    exact hx1
  have h5 : ∀ x, f x x = 1 := by
    intro x
    specialize h4 x x
    simpa using h4
  have h6 : ∀ x, f x (-x) = 1 := by
    intro x
    specialize h4 x (-x)
    simpa using h4
  have h7 : ∀ x y, f x y * f y x = 1 := by
    intro x y
    have hx : f x y = 1 := h4 x y
    have hy : f y x = 1 := h4 y x
    rw [hx, hy]
    all_goals norm_num
  exact ⟨h5, h6, h7⟩