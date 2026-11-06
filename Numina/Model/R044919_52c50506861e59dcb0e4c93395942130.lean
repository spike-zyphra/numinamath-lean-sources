import Mathlib

theorem algebra_601274 {f : ℚ → ℚ → ℝ}
    (hpos : ∀ x y, f x y > 0)
    (h1 : ∀ x y z, f (x * y) z = f x z * f y z)
    (h2 : ∀ z x y, f z (x * y) = f z x * f z y)
    (h3 : ∀ x, f x (1 - x) = 1) :
    (∀ x, f x x = 1) ∧ (∀ x, f x (-x) = 1) ∧
    (∀ x y, f x y * f y x = 1) := by 
  have h4 : ∀ z, f 0 z = 1 := by
    intro z 
    have eq1 := h1 0 0 z
    norm_num at eq1 
    have eq2 : f 0 z * (f 0 z - 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp eq2) with h h'
    · -- Case $h : f 0 z = 0$
      linarith [hpos 0 z, h]
    · -- Case $h' : f 0 z -1 =0$, so h' : f 0 z = 1
      linarith 
  have h5 : ∀ x z, f x z = 1 := by 
    intro x z 
    have eq1 := h1 x 0 z 
    simp [show f 0 z = 1 by apply h4] at eq1 
    linarith 
  constructor 
  · -- Show that ∀ x, f x x = 1
    intro x
    specialize h5 x x 
    linarith 
  constructor 
  · -- Show that ∀ x, f x (-x) = 1 
    intro x 
    specialize h5 x (-x) 
    linarith 
  · -- Show that ∀ x y, f x y * f y x = 1 
    intro x y 
    have eq1 : f x y = 1 := h5 x y 
    have eq2 : f y x = 1 := h5 y x 
    rw [eq1, eq2] 
    all_goals norm_num