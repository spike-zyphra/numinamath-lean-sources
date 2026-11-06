import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_296825 :
  IsLeast {d | ∃ x y : ℝ, y^2 = 2 * x ∧ d = abs (x + y + 1) / sqrt 2} (sqrt 2 / 4) := by 
  constructor 
  · -- First part: proving sqrt(2)/4 is achievable
    use 1 / 2, -1 
    constructor 
    · -- Show that (-1)^2 = 2 * (1/2)
      norm_num 
    · -- Show that sqrt(2)/4 = abs ((1/2) + (-1) + 1) / sqrt 2 
      have h1 : abs ((1 / 2 : ℝ) + (-1) + 1) = 1 / 2 := by 
        norm_num [abs_of_nonneg]
      rw [h1]
      have h2 : sqrt 2 / 4 = (1 / 2) / sqrt 2 := by 
        field_simp
        <;> ring_nf <;> norm_num 
      rw [h2] 
  · -- Second part: proving sqrt(2)/4 is a lower bound
    intro d hd
    rcases hd with ⟨x, y, h_eq, hd_eq⟩ 
    have h1 : abs (x + y + 1) ≥ 1 / 2 := by 
      have h_eq_x : x = y^2 / 2 := by 
        linarith [h_eq]
      rw [h_eq_x]
      have h3 : y^2 / 2 + y + 1 ≥ 0 := by 
        nlinarith [sq_nonneg (y + 1)]
      have h6 : abs (y^2 / 2 + y + 1) = y^2 / 2 + y + 1 := abs_of_nonneg h3
      have h4 : y^2 / 2 + y + 1 ≥ 1 / 2 := by 
        nlinarith [sq_nonneg (y + 1)]
      rw [h6]
      linarith
    have h4 : abs (x + y + 1) / sqrt 2 ≥ (1 / 2) / sqrt 2 := by 
      apply (div_le_div_right (by positivity)).2 
      linarith
    have h5 : (1 / 2) / sqrt 2 = sqrt 2 / 4 := by 
      field_simp 
      <;> ring_nf <;> norm_num 
    linarith [hd_eq, h4, h5]