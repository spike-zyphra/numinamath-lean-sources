import Mathlib

open Real Set
open scoped Real

theorem algebra_3071 {x : ℝ} (hx : x ∈ Icc 0 1) :
    2 * arctan (sqrt x) = arccos ((1 - x) / (1 + x)) := by 
  rcases hx with ⟨hx0, hx1⟩
  have h1 : 0 ≤ x := hx0
  have h2 : x ≤ 1 := hx1
  have h6 : -1 ≤ (1 - x) / (1 + x) ∧ (1 - x) / (1 + x) ≤ 1 := by
    constructor
    · -- Show -1 ≤ (1 - x) / (1 + x)
      have h7 : 0 < (1 + x : ℝ) := by
        nlinarith
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith
    · -- Show (1 - x) / (1 + x) ≤ 1
      have h7 : 0 < (1 + x : ℝ) := by
        nlinarith
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
  have h5 : cos (2 * arctan (sqrt x)) = (1 - x) / (1 + x) := by
    have h7 : cos (2 * arctan (sqrt x)) = 2 * (cos (arctan (sqrt x))) ^ 2 - 1 := by
      rw [cos_two_mul]
    have h8 : cos (arctan (sqrt x)) = 1 / Real.sqrt (1 + x) := by
      have h9 : cos (arctan (sqrt x)) = 1 / Real.sqrt (1 + (sqrt x) ^ 2) := by
        rw [cos_arctan]
      rw [h9]
      have h10 : (sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ x by linarith)
      have h11 : (1 + (sqrt x) ^ 2 : ℝ) = (1 + x : ℝ) := by
        nlinarith [h10]
      rw [h11]
    rw [h7, h8]
    have h9 : ((1 / Real.sqrt (1 + x) : ℝ) ) ^ 2 = 1 / (1 + x) := by
      have h10a : (Real.sqrt (1 + x)) ^ 2 = 1 + x := Real.sq_sqrt (show 0 ≤ (1 + x : ℝ) by linarith)
      field_simp [h10a]
    rw [h9]
    have h11 : 2 * (1 / (1 + x : ℝ) ) - 1 = (1 - x) / (1 + x : ℝ) := by
      have h12 : (1 + x : ℝ) ≠ 0 := by linarith
      field_simp [h12]
      <;> nlinarith
    linarith [h11]
  have ha1 : 0 ≤ 2 * arctan (sqrt x) := by
    have h10 : 0 ≤ arctan (sqrt x) := by
      have h2 : sqrt x ≥ 0 := Real.sqrt_nonneg x
      have h5 : arctan (sqrt x) ≥ arctan (0 : ℝ) := by
        apply Real.arctan_le_arctan
        all_goals nlinarith [h2]
      have h6 : arctan (0 : ℝ) = 0 := by
        simp [arctan_zero]
      linarith [h5, h6]
    linarith
  have ha2 : 2 * arctan (sqrt x) ≤ Real.pi := by
    have h12 : arctan (sqrt x) ≤ Real.pi / 4 := by
      have h13 : sqrt x ≤ (1 : ℝ) := by
        have h14 : x ≤ (1 : ℝ) := hx1
        have h15 : sqrt x ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h16 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
        linarith [h15, h16]
      have h17 : arctan (sqrt x) ≤ arctan (1 : ℝ) := by
        apply Real.arctan_le_arctan
        nlinarith [Real.sqrt_nonneg x, h13]
      have h18 : arctan (1 : ℝ) = Real.pi / 4 := by
        exact arctan_one
      linarith [h18, h17]
    nlinarith [Real.pi_pos]
  have eq1 : 2 * arctan (sqrt x) = arccos ((1 - x) / (1 + x)) := by
    have h13 : cos (2 * arctan (sqrt x)) = (1 - x) / (1 + x) := h5
    have h14 : arccos (cos (2 * arctan (sqrt x)) ) = 2 * arctan (sqrt x) := by
      rw [Real.arccos_cos]
      all_goals linarith [ha1, ha2]
    have eq2 : arccos (cos (2 * arctan (sqrt x)) ) = arccos ((1 - x) / (1 + x)) := by
      rw [h13]
    linarith [h14, eq2]
  exact_mod_cast eq1