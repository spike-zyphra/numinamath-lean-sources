import Mathlib

theorem inequalities_5392 (x : ℕ) (hx : 0 < x) :
    7 * x - 37 < (2 * x / 3 : ℝ) + 8 ↔ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by
  constructor
  · -- Assume the inequality holds, prove the disjunction of equations
    intro h
    have h1 : (x : ℝ) > 0 := by exact_mod_cast hx
    have h2 : (7 * (x : ℝ) - 37) < (2 * (x : ℝ) / 3 + 8) := by 
      simpa using h
    have h3 : (x : ℝ) < (135 / 19 : ℝ) := by 
      linarith
    have h4 : x < 8 := by
      by_contra h5
      push_neg at h5
      have h5' : (x : ℝ) >= (8 : ℝ) := by exact_mod_cast h5
      nlinarith
    interval_cases x <;> norm_num at h ⊢ <;> tauto
  · -- Assume one of the equations holds, prove the inequality
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num