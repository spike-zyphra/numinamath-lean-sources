import Mathlib

theorem algebra_162528 {n : ℕ} (hn : n > 0) (h : (n * 2) * (5 / 7 : ℚ) = n * (2 / 7 : ℚ)) :
    n + 2 * n = 9 := by
  have eq4 : (n * (2 : ℚ)) * (5 / 7 : ℚ) = (n * (2 / 7 : ℚ)) := by
    simpa using h
  have eq5 : (n : ℚ) * (10 : ℚ) = (n : ℚ) * (2 : ℚ) := by
    have eq6 : (n * (2 : ℚ) ) * (5 / 7 : ℚ) = (n * (2 / 7 : ℚ)) := eq4
    have eq9 : (n * (2 : ℚ) ) * (5 / 7 : ℚ) = (10 * (n : ℚ) ) / 7 := by
      field_simp
      <;> ring
    have eq10 : (n * (2 / 7 : ℚ)) = (2 * (n : ℚ) ) / 7 := by
      field_simp
      <;> ring
    rw [eq9] at eq6
    rw [eq10] at eq6
    have eq11 : 10 * (n : ℚ) = 2 * (n : ℚ) := by
      linarith [eq6]
    calc
      (n : ℚ) * (10 : ℚ) = (10 * (n : ℚ)) := by ring
      _ = (2 * (n : ℚ)) := by linarith [eq11]
      _ = (n : ℚ) * (2 : ℚ) := by ring
  have eq6 : (n : ℚ) * (8 : ℚ) = 0 := by
    linarith [eq5]
  have eq7 : (n : ℚ) = 0 := by 
    cases' (mul_eq_zero.mp eq6) with h8 h9
    · -- case where (n : ℚ) = 0
      linarith
    · -- case where (8 : ℚ) = 0
      exfalso
      norm_num at h9
  have h10 : (n : ℚ) > (0 : ℚ) := by 
    exact_mod_cast hn
  have eq8 : (n : ℚ) = (0 : ℚ) := eq7
  linarith