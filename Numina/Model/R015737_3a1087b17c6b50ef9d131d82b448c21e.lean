import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_299154 :
  IsGreatest {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = min a (b / (a ^ 2 + b ^ 2))} (Real.sqrt 2 / 2) := by

  constructor
  · -- First part: show `Real.sqrt 2 / 2` is in the set.
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    constructor
    · -- Show that `0 < Real.sqrt 2 / 2`
      have h1 : 0 < Real.sqrt 2 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith [Real.sqrt_nonneg 2]
    constructor
    · -- Show that `0 < Real.sqrt 2 / 2`
      have h1 : 0 < Real.sqrt 2 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith [Real.sqrt_nonneg 2]
    · -- Show that `Real.sqrt 2 / 2 = min (Real.sqrt 2 / 2) ( (Real.sqrt 2 / 2) / ((Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2) )`
      have h1 : (Real.sqrt 2 / 2 : ℝ) / ((Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2) = Real.sqrt 2 / 2 := by
        have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (2 : ℝ) / 4 := by
          calc
            (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 / 4 := by ring_nf
            _ = (2 : ℝ) / 4 := by
              rw [Real.sq_sqrt]
              all_goals linarith
        have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 + (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 : ℝ) := by
          rw [h2]
          norm_num
        rw [h3]
        all_goals field_simp
      rw [h1]
      all_goals
        norm_num
  · -- Second part: show `Real.sqrt 2 / 2` is the greatest element in the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ a := by
      cases min_cases a (b / (a ^ 2 + b ^ 2)) with
      | inl h2 =>
        linarith
      | inr h2 =>
        linarith
    have h2 : x ≤ b / (a ^ 2 + b ^ 2) := by 
      cases min_cases a (b / (a ^ 2 + b ^ 2)) with
      | inl h1 =>
        linarith
      | inr h1 =>
        linarith
    have h3 : a > Real.sqrt 2 / 2 := by 
      linarith [h1, h]
    have h4 : b / (a ^ 2 + b ^ 2) > Real.sqrt 2 / 2 := by 
      linarith [h2, h]
    have h5 : a ^ 2 + b ^ 2 > 0 := by positivity
    have h6 : 2 * b > Real.sqrt 2 * (a ^ 2 + b ^ 2) := by 
      have h7 : b / (a ^ 2 + b ^ 2) > Real.sqrt 2 / 2 := h4
      have h8 : 0 < a ^ 2 + b ^ 2 := by positivity
      apply (lt_div_iff₀ h8).mp at h7 
      nlinarith
    nlinarith [sq_nonneg (a - Real.sqrt 2 / 2), sq_nonneg (b - Real.sqrt 2 / 2), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), 
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), 
      mul_pos ha hb
    ]