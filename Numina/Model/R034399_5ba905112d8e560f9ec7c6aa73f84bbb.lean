import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_106925 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x - π - ⌊x / π⌋ - abs (sin x)) :
  IsGreatest (range f) (f (π / 2)) → False := by
  intro h
  have h1 : ∀ y, y ∈ range f → y ≤ f (π / 2) := by
    apply h.2
  have h2 : f (3 * π / 2) ≤ f (π / 2) := by 
    have h3 : f (3 * π / 2) ∈ range f := by 
      simpa using ⟨3 * π / 2, by simp⟩
    have h4 := h1 (f (3 * π / 2)) h3
    simpa using h4
  have h3 : f (3 * π / 2) = 3 * π / 2 - π - ⌊(3 * π / 2) / π⌋ - abs (sin (3 * π / 2)) := by 
    apply h₀
  have h4 : f (π / 2) = π / 2 - π - ⌊(π / 2) / π⌋ - abs (sin (π / 2)) := by 
    apply h₀
  have h5 : ⌊(3 * π / 2) / π⌋ = 1 := by
    have h6 : π > 0 := Real.pi_pos
    have h7 : (3 * π / 2) / π = 3 / 2 := by
      field_simp
      <;> nlinarith [Real.pi_pos]
    rw [h7]
    norm_num [Int.floor_eq_iff]
  have h8 : ⌊(π / 2) / π⌋ = 0 := by
    have h6 : π > 0 := Real.pi_pos
    have h7 : (π / 2) / π = 1 / 2 := by
      field_simp
      <;> nlinarith [Real.pi_pos]
    rw [h7]
    norm_num [Int.floor_eq_iff]
  have h9 : sin (3 * π / 2) = -1 := by 
    have h6 : 3 * π / 2 = π + π / 2 := by 
      nlinarith
    rw [h6]
    have h7 : sin (π + π / 2) = -1 := by
      rw [sin_add]
      simp [sin_pi, cos_pi]
      all_goals linarith
    linarith
  have h10 : sin (π / 2) = 1 := by 
    exact sin_pi_div_two
  have eq1 : f (3 * π / 2) = π / 2 - 2 := by
    rw [h3, h5, h9]
    all_goals
      norm_num [abs_of_nonneg, abs_of_nonpos]
      <;> nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
  have eq2 : f (π / 2) = -π / 2 - 1 := by
    rw [h4, h8, h10]
    all_goals
      norm_num [abs_of_nonneg, abs_of_nonpos]
      <;> nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]
  have h11 : π / 2 - 2 ≤ -π / 2 - 1 := by 
    linarith [h2, eq1, eq2]
  nlinarith [Real.pi_pos, Real.pi_gt_31415, Real.pi_lt_31416]