import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_179832 (a : ℝ) :
  (∀ x ∈ Icc 1 2, abs (2^x - a) < abs (5 - 2^x)) ↔ 3 < a ∧ a < 5 := by
  constructor
  · -- Forward implication: if the inequality holds ∀ x ∈ [1, 2], then 3 < a ∧ a < 5.
    intro h
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    have h3 : abs (2 ^ (1 : ℝ) - a) < abs (5 - 2 ^ (1 : ℝ)) := by
      simpa using h1
    have h4 : abs (2 ^ (2 : ℝ) - a) < abs (5 - 2 ^ (2 : ℝ)) := by
      simpa using h2
    -- Then compute these specific values
    have h5 : abs (2 ^ (1 : ℝ) - a) = abs (2 - a) := by
      norm_num
    have h6 : abs (5 - 2 ^ (1 : ℝ)) = abs (5 - (2 : ℝ)) := by
      norm_num
    have h7 : abs (2 ^ (2 : ℝ) - a) = abs (4 - a) := by
      norm_num
    have h8 : abs (5 - 2 ^ (2 : ℝ)) = abs (5 - (4 : ℝ)) := by
      norm_num
    rw [h5, h6] at h3
    rw [h7, h8] at h4
    -- From these inequalities
    have h9 : abs (2 - a) < (3 : ℝ) := by
      rw [show abs (5 - (2 : ℝ)) = 3 by norm_num [abs_of_pos]] at h3
      linarith
    have h10 : abs (4 - a) < (1 : ℝ) := by
      rw [show abs (5 - (4 : ℝ)) = 1 by norm_num [abs_of_pos]] at h4
      linarith
    -- Then conclude that
    have ha1 : 3 < a := by
      linarith [abs_lt.mp h10]
    have ha2 : a < 5 := by
      linarith [abs_lt.mp h10]
    constructor
    · exact ha1
    · exact ha2
  · -- Reverse implication: if 3 < a ∧ a < 5, then ∀ x ∈ [1, 2], abs (2^x - a) < abs (5 - 2^x).
    rintro ⟨ha1, ha2⟩
    intro x hx
    -- For all x ∈ [1, 2]
    have hx1 : 1 ≤ x := by
      simpa using hx.1
    have hx2 : x ≤ 2 := by
      simpa using hx.2
    have h31 : (1 : ℕ) ≤ x := by
      omega
    have h32 : x ≤ (2 : ℕ) := by
      omega
    have h312 : (x : ℝ) ≥ (1 : ℝ) := by
      exact_mod_cast h31
    have h322 : (x : ℝ) ≤ (2 : ℝ) := by
      exact_mod_cast h32
    -- Real power of 2
    have h33 : (2 : ℝ) ^ (x : ℝ) ≥ (2 : ℝ) := by
      have h3412 : (2 : ℝ) ^ (x : ℝ) ≥ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals
          try { norm_num at h312 ⊢ }
          try { tauto }
          all_goals try { linarith [h312] }
      have h34 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
        norm_num
      have h35 : (2 : ℝ) ^ (x : ℝ) ≥ (2 : ℝ) ^ (1 : ℝ) := h3412
      rw [h34] at h35
      linarith
    have h34 : (2 : ℝ) ^ (x : ℝ) ≤ (4 : ℝ) := by
      have h3451 : (2 : ℝ) ^ (x : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        all_goals
          try { norm_num at h322 ⊢ }
          try { tauto }
          all_goals try { linarith [h322] }
      have h35 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by
        norm_num
      have h36 : (2 : ℝ) ^ (x : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) := h3451
      rw [h35] at h36
      linarith
    -- Now we know 2 ≤ 2 ^ x ≤ 4
    have h9 : abs ((2 : ℝ) ^ (x : ℝ) - a) < abs (5 - (2 : ℝ) ^ (x : ℝ)) := by
      by_cases h10 : ((2 : ℝ) ^ (x : ℝ)) ≥ a
      · -- If (2 : ℝ) ^ (x : ℝ) ≥ a, then (2^x - a) ≥ 0
        rw [abs_of_nonneg (by linarith)]
        by_cases h20 : (5 - (2 : ℝ) ^ (x : ℝ)) ≥ (0 : ℝ)
        · -- If (5 - 2^x) ≥ 0
          rw [abs_of_nonneg (by linarith)]
          all_goals nlinarith
        · -- If (5 - 2^x) < 0
          rw [abs_of_neg (by linarith)]
          all_goals nlinarith
      · -- If (2 : ℝ) ^ (x : ℝ) < a, then (2^x - a) < 0
        rw [abs_of_neg (by linarith)]
        by_cases h20 : (5 - (2 : ℝ) ^ (x : ℝ)) ≥ (0 : ℝ)
        · -- If (5 - 2^x) ≥ 0
          rw [abs_of_nonneg (by linarith)]
          all_goals nlinarith
        · -- If (5 - 2^x) < 0
          rw [abs_of_neg (by linarith)]
          all_goals nlinarith
    simpa using h9