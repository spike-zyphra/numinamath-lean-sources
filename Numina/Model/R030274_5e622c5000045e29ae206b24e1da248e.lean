import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_269116 {f : ℝ → ℝ} (hf : f = λ x => sqrt 3 * cos x - sin x)
  (m : ℝ) (hm : m > 0) (h : ∀ x, f (x - m) = f (-x + m)) :
  IsLeast {x | 0 < x ∧ (∀ y, f (y - x) = f (-y + x))} (5 * π / 6) := by
  -- deriving the IsLeast from inconsistency (h : ∀ x, f (x - m) = f (-x + m))
  -- since it leads to contradiction with hm
  have eq1 := h 0 
  simp [show 0 - m = -m by ring, 
        show - (0 : ℝ) + m = m by ring] at eq1
  have eq2 : f (-m) = f m := by 
    simpa using eq1
  rw [hf] at eq2 
  simp [sin_neg, cos_neg] at eq2 
  have h3 : sin m = 0 := by 
    nlinarith 
  have eq3 := h (m + Real.pi / 2) 
  have eq4 : f ( (m + Real.pi / 2 ) - m ) = f ( - (m + Real.pi / 2 ) + m ) := by 
    simpa using eq3 
  have eq5 : f ( (m + Real.pi / 2 ) - m ) = f (Real.pi / 2) := by 
    have eq6 : (m + Real.pi / 2 ) - m = Real.pi / 2 := by 
      linarith 
    rw [eq6] 
  have eq7 : f ( - (m + Real.pi / 2 ) + m ) = f (- (Real.pi / 2 ) ) := by
    have eq8 : - (m + Real.pi / 2 ) + m = - (Real.pi / 2 ) := by 
      linarith 
    rw [eq8] 
  rw [eq5, eq7] at eq4 
  have eq6 : f (Real.pi / 2) = f (- (Real.pi / 2 ) ) := by 
    linarith [eq4] 
  rw [hf] at eq6 
  simp [sin_neg, cos_neg, Real.sin_pi_div_two, Real.cos_pi_div_two] at eq6 
  all_goals linarith