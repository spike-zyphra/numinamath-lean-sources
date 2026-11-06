import Mathlib

theorem algebra_8030 (a b : ℚ) (h : ∀ x : ℝ, (a * x + abs b) / 3 = (x + a * b) / 2 + 1) :
    a = 3 / 2 ∧ b = -12 / 13 := by 
  have eq4 := h 0
  have eq5 := h 1
  have eq6 := h (2 : ℝ)
  by_cases hb : (b : ℝ) ≥ 0
  · -- If b ≥ 0, then |b| = b.
    have h1 : abs (b : ℝ) = (b : ℝ) := by
      rw [abs_of_nonneg hb]
    simp [h1] at eq4 eq5 eq6
    have ha : (a : ℝ) = 3 / 2 := by
      ring_nf at eq4 eq5 eq6
      linarith
    have hb' : (b : ℝ) = -12 / 5 := by
      rw [ha] at eq4
      nlinarith
    have h7 : (b : ℝ) ≥ 0 := hb
    nlinarith
  · -- If b < 0, then |b| = -b.
    have h1 : abs (b : ℝ) = - (b : ℝ) := by 
      rw [abs_of_neg (show (b : ℝ) < 0 by linarith)]
    simp [h1] at eq4 eq5 eq6
    have ha : (a : ℝ) = 3 / 2 := by
      ring_nf at eq4 eq5 eq6
      linarith
    have hb' : (b : ℝ) = -12 / 13 := by
      rw [ha] at eq4
      nlinarith
    constructor
    · -- Show that a = 3/2
      exact_mod_cast (show (a : ℝ) = (3 / 2 : ℚ) by
        rw [ha]
        all_goals norm_num
      )
    · -- Show that b = -12/13
      exact_mod_cast (show (b : ℝ) = (-12 / 13 : ℚ) by 
        rw [hb']
        all_goals norm_num
      )