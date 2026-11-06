import Mathlib

theorem algebra_12376 : IsLeast {z : ℕ | ∃ x y : ℕ, x ≠ y ∧ 0 < x ∧ 0 < y ∧
    (1 / x : ℚ) + 1 / y = 1 / 18 ∧ z = x + y} 75 := by 
  constructor
  · -- First part: Show that 75 is in the set
    use 30, 45
    all_goals norm_num
  · -- Second part: Show that 75 is minimal
    intro z h 
    rcases h with ⟨x, y, hxy, hx, hy, heq, hz⟩ 
    by_contra h
    push_neg at h 
    have h1 : z < 75 := h 
    rw [show z = x + y by omega] at h1 
    have h2 : x + y < 75 := h1 
    have eq1 : (x : ℚ) * (y : ℚ) = 18 * ((x : ℚ) + (y : ℚ)) := by 
      field_simp at heq ⊢ 
      nlinarith 
    have eq2 : (x : ℕ) * (y : ℕ) = 18 * ((x : ℕ) + (y : ℕ)) := by 
      exact_mod_cast eq1 
    have h5 : x ≤ 74 := by omega 
    have h6 : y ≤ 74 := by omega 
    interval_cases x <;> omega