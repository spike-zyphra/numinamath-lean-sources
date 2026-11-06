import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22185 :
  IsLeast {x | ∃ a b c : ℝ, a ∈ Icc 1 2 ∧ b ∈ Icc 1 2 ∧ c ∈ Icc 1 2 ∧ a + b + c = 5 ∧ x = 1/(a+b) + 1/(b+c)} (4/7) := by 
  constructor
  · -- Show that 4/7 is in the set
    use 1.5, 2, 1.5 
    constructor
    · -- Show that 1.5 ∈ [1, 2]
      exact ⟨by norm_num, by norm_num⟩
    constructor 
    · -- Show that 2 ∈ [1, 2]
      exact ⟨by norm_num, by norm_num⟩
    constructor 
    · -- Show that 1.5 ∈ [1, 2]
      exact ⟨by norm_num, by norm_num⟩
    constructor 
    · -- Show that 1.5 + 2 + 1.5 = 5
      norm_num 
    · -- Show that x = 1/(a + b) + 1/(b + c)
      norm_num 
  · -- Show that 4/7 is the least of the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, heq, hx⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    have h1 : 0 < a + b := by 
      nlinarith 
    have h2 : 0 < b + c := by 
      nlinarith 
    have h : 1 / (a + b) + 1 / (b + c) ≥ 4 / 7 := by
      have h3 : (a + b) * (b + c) > 0 := by 
        nlinarith 
      have h4 : (1 / (a + b) + 1 / (b + c) - 4 / 7) ≥ 0 := by 
        have h5 : (1 / (a + b) + 1 / (b + c) - 4 / 7) = (7 * ((a + b) + (b + c)) - 4 * ((a + b) * (b + c))) / (7 * (a + b) * (b + c)) := by 
          field_simp 
          ring 
        rw [h5] 
        apply div_nonneg 
        nlinarith [sq_nonneg (a - 1.5), sq_nonneg (c - 1.5), sq_nonneg (b - 2), 
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), 
          mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb2), 
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc2), 
          mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr ha2), 
          mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc2), 
          mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc1), 
          mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2)]
        all_goals nlinarith 
      linarith 
    linarith