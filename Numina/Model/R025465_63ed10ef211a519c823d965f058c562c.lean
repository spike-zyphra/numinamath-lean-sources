import Mathlib

theorem algebra_308065 (a : ℝ) (ha : a^2 - 2002 * a + 1 = 0) :
    a^2 - 2001 * a + 2002 / (a^2 + 1) = 2001 := by
  have ha1 : a ≠ 0 := by 
    by_contra h
    rw [h] at ha
    nlinarith
  have eq1 : a^2 + 1 = 2002 * a := by linarith
  have eq2 : 2002 / (a^2 + 1) = 1 / a := by
    have h2 : a^2 + 1 = 2002 * a := eq1
    rw [h2]
    have ha1' : a ≠ 0 := ha1
    field_simp [ha1']
    <;> nlinarith
  have eq3 : 1 / a = 2002 - a := by
    have ha1' : a ≠ 0 := ha1
    field_simp [ha1']
    nlinarith [ha]
  have eq4 : a^2 - 2001 * a + 2002 / (a^2 + 1) = a^2 - 2001 * a + (1 / a) := by
    rw [eq2]
    all_goals linarith
  rw [eq4]
  rw [eq3]
  have eq5 : a^2 - 2002 * a = -1 := by
    nlinarith [ha]
  nlinarith [eq5, ha]