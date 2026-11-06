import Mathlib

theorem algebra_106097 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - x - 6) :
    IsLeast {d | ∃ x y, d = abs (x - y) ∧ f x = 6 ∧ f y = -6} 3 := by 
  constructor
  · -- Show that 3 is in the set
    use 4, 1
    constructor
    · -- Calculate |4 - 1| = 3
      norm_num [abs]
    constructor
    · -- Check that f(4) = 6
      norm_num [hf]
    · -- Check that f(1) = -6
      norm_num [hf]
  · -- Show that 3 is the least element in the set
    intro d hd
    rcases hd with ⟨x, y, h1, h2, h3⟩
    have eq1 : x ^ 2 - x - 6 = 6 := by
      rw [hf] at h2
      simpa using h2
    have eq2 : y ^ 2 - y - 6 = -6 := by
      rw [hf] at h3
      simpa using h3
    have hx : x = 4 ∨ x = -3 := by
      have h1 : x^ 2 - x - 12 = 0 := by nlinarith
      have : (x - 4) * (x + 3) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp this) with h5 h6
      · -- x - 4 = 0
        left
        linarith
      · -- x + 3 = 0
        right
        linarith
    have hy : y = 0 ∨ y = 1 := by
      have h2 : y^2 - y = 0 := by nlinarith
      have : y * (y - 1) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp this) with h7 h8
      · -- y = 0
        left
        nlinarith
      · -- y - 1 = 0
        right
        nlinarith
    rcases hx with (rfl | rfl)
    · -- x = 4
      rcases hy with (rfl | rfl)
      · -- y = 0
        norm_num [abs] at h1
        linarith
      · -- y = 1
        norm_num [abs] at h1
        linarith
    · -- x = -3
      rcases hy with (rfl | rfl)
      · -- y = 0
        norm_num [abs] at h1
        linarith
      · -- y = 1
        norm_num [abs] at h1
        linarith