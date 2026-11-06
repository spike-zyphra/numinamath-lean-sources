import Mathlib
open Real
theorem algebra_11771 : {x : ℝ | 1 / ((x - 1) * (x - 2)) + 1 / ((x - 2) * (x - 3)) + 1 / ((x - 3) * (x - 4)) = 1 / 6} =
{7, -2}:= by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward implication: from the equation to {7, -2}
    intro h
    have h1 : x - 1 ≠ 0 := by
      by_contra h1
      have : x = 1 := by linarith
      rw [this] at h
      norm_num at h
    have h2 : x - 2 ≠ 0 := by
      by_contra h4
      have : x = 2 := by linarith
      rw [this] at h
      norm_num at h
    have h3 : x - 3 ≠ 0 := by
      by_contra h4
      have : x = 3 := by linarith
      rw [this] at h
      norm_num at h
    have h4 : x - 4 ≠ 0 := by
      by_contra h4
      have : x = 4 := by linarith
      rw [this] at h
      norm_num at h
    have eq0 : 1 / ((x - 1) * (x - 2)) + 1 / ((x - 2) * (x - 3)) + 1 / ((x - 3) * (x - 4)) = -1 / (x - 1) + 1 / (x - 4) := by
      have eq1 : 1 / ((x - 1) * (x - 2)) = 1 / (x - 2) - 1 / (x - 1) := by
        field_simp [(show x - 1 ≠ 0 by assumption), (show x - 2 ≠ 0 by assumption)]
        <;> ring
      have eq2 : 1 / ((x - 2) * (x - 3)) = 1 / (x - 3) - 1 / (x - 2) := by
        field_simp [(show x - 2 ≠ 0 by assumption), (show x - 3 ≠ 0 by assumption)]
        <;> ring
      have eq3 : 1 / ((x - 3) * (x - 4)) = 1 / (x - 4) - 1 / (x - 3) := by
        field_simp [(show x - 3 ≠ 0 by assumption), (show x - 4 ≠ 0 by assumption)]
        <;> ring
      rw [eq1, eq2, eq3]
      field_simp [(show x - 1 ≠ 0 by assumption), (show x - 2 ≠ 0 by assumption), (show x - 3 ≠ 0 by assumption), (show x - 4 ≠ 0 by assumption)]
      <;> ring 
      <;> norm_num
      <;> norm_num
      <;> norm_num
      <;> norm_num
    rw [eq0] at h
    have h5 : -1 / (x - 1) + 1 / (x - 4) - 1 / 6 = 0 := by linarith
    have h6 : -6 * (x - 4) + 6 * (x - 1) - (x - 1) * (x - 4) = 0 := by
      field_simp [(show x - 1 ≠ 0 by assumption), (show x - 4 ≠ 0 by assumption)] at h5
      nlinarith [sq_pos_of_ne_zero (show x - 1 ≠ 0 by assumption), sq_pos_of_ne_zero (show x - 4 ≠ 0 by assumption), sq_pos_of_pos (show (0:ℝ) < 2 by norm_num), sq_pos_of_pos (show (0:ℝ) < 3 by norm_num), sq_pos_of_pos (show (0:ℝ) < 4 by norm_num)]
    have h7 : x ^ 2 - 5 * x - 14 = 0 := by
      nlinarith 
    have h8 : (x - 7) * (x + 2) = 0 := by 
      nlinarith 
    cases' mul_eq_zero.mp h8 with h9 h10
    · -- Case x - 7 = 0 so x = 7
      left 
      linarith 
    · -- Case x + 2 = 0 so x = -2
      right 
      linarith 
  · -- Backward implication: {7, -2} satisfy the equation
    rintro (rfl | rfl)
    · -- Case x = 7
      norm_num 
    · -- Case x = -2
      norm_num