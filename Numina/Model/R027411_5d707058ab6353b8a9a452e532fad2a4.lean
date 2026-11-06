import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_158416 {F : ℝ → ℝ}
  (hF : F = λ x => 1 / 2 + (1 / Real.pi) * arctan (x / 2)) :
  ∃ x, F x = 3 / 4 ∧ ∀ y, F y ≤ 3 / 4 → y ≤ x := by
  use 2
  constructor
  · -- Show that F(2) = 3/4.
    rw [hF]
    have h1 : arctan (2 / 2) = Real.pi / 4 := by
      rw [show (2 / 2 : ℝ) = 1 by norm_num]
      rw [arctan_one]
      all_goals try linarith [Real.pi_pos]
      all_goals try tauto
    norm_num [h1]
    <;> field_simp <;> nlinarith [Real.pi_pos]
  · -- Show that ∀ y, F y ≤ 3/4 → y ≤ 2.
    intro y h
    rw [hF] at h 
    have h2 : 1 / 2 + (1 / Real.pi) * arctan (y / 2) ≤ 3 / 4 := by 
      simpa using h 
    -- Derive h4 from h2.
    -- (1 / Real.pi) * arctan (y / 2) ≤ 3 / 4 - 1 / 2 = 1 / 4
    have h4 : (1 / Real.pi) * arctan (y / 2) ≤ 1 / 4 := by
      nlinarith 
    by_contra h6
    push_neg at h6 
    -- Assume y > 2, derive a contradiction with h4.
    -- Assume y > 2, so y / 2 > 1, then arctan (y / 2) > Real.pi / 4.
    have h7 : arctan (y / 2) > Real.pi / 4 := by
      have h8 : y / 2 > (1 : ℝ) := by
        linarith 
      have h9 : arctan (y / 2) > arctan (1 : ℝ) := by
        apply Real.arctan_strictMono
        all_goals
        linarith 
      have h10 : arctan (1 : ℝ) = Real.pi / 4 := by 
        rw [arctan_one]
        all_goals try linarith 
      linarith 
    -- From h7 : arctan (y / 2) > Real.pi / 4
    -- Derive that (1 / Real.pi) * arctan (y / 2) > (1 / 4).
    have h11 : (1 / Real.pi : ℝ) * arctan (y / 2) > (1 / 4 : ℝ) := by
      have h12 : arctan (y / 2) > Real.pi / 4 := h7
      -- Multiply through by Real.pi (positive)
      have h13 : (1 / Real.pi : ℝ) * arctan (y / 2) > (1 / Real.pi : ℝ) * (Real.pi / 4 : ℝ) := by
        apply mul_lt_mul_of_pos_left 
        linarith 
        positivity
      have h14 : (1 / Real.pi : ℝ) * (Real.pi / 4 : ℝ) = (1 / 4 : ℝ) := by 
        field_simp
        <;> ring_nf <;> try norm_num 
      linarith 
    linarith 
    all_goals try norm_num 
    all_goals try linarith 
    all_goals norm_num 
    all_goals try norm_num