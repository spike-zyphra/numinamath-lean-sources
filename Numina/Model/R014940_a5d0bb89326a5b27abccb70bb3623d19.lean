import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_115505 (a : ℝ) (B : Set ℝ)
  (hB : B = {x | x^2 - 2*a*x + a ≤ 0}) :
  (Ioc 0 3) ∪ B = Ioc 0 3 ↔ 0 < a ∧ a ≤ 9/5 := by
  constructor
  · -- Forward implication: From (Ioc 0 3) ∪ B = Ioc 0 3, prove 0 < a ∧ a ≤ 9/5
    intro h
    have h1 : B ⊆ Ioc 0 3 := by
      rw [Set.union_eq_left] at h
      simpa using h
    have h2 : ∀ x, x ∈ B → x ∈ Ioc 0 3 := by
      intro x hx
      exact h1 hx
    have h31 : 0 < a := by
      by_contra h4
      push_neg at h4
      by_cases h32 : a < (0 : ℝ)
      · -- Assume a < 0
        have h32 : a < (0 : ℝ) := h32
        have h5 : (a - Real.sqrt (a ^ 2 - a)) ∈ B := by
          rw [hB]
          simp
          nlinarith [Real.sqrt_nonneg (a ^ 2 - a), Real.sq_sqrt (show (a ^ 2 - a) ≥ 0 by nlinarith [sq_nonneg (a * (a * (-1 : ℝ))), sq_nonneg (a * (a - 1 : ℝ)), sq_nonneg ((a) - 0), sq_nonneg (a * (a * (-1 : ℝ))) ]), sq_nonneg (a * (a * 1 / 5)), sq_nonneg ( (a : ℝ) ), sq_nonneg ( (a - 0) * (a - 10) ) ]
        have h6 : (a - Real.sqrt (a ^ 2 - a)) ∈ Ioc 0 3 := by
          apply h2
          exact h5
        have h71 : 0 < (a - Real.sqrt (a ^ 2 - a)) := by
          have h711 := h6.left
          try { tauto }
          <;> norm_num at h711 ⊢
          <;> nlinarith
        have h72 : Real.sqrt (a ^ 2 - a) > a := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 - a), sq_nonneg (a), sq_nonneg (Real.sqrt (a ^ 2 - a)), Real.sq_sqrt (show (a ^ 2 - a) ≥ 0 by nlinarith [sq_nonneg (a * (a * (-1 : ℝ))), sq_nonneg ((a + 1) * (a + 1) * (-1) * (-1)), sq_nonneg ((a * (a * (-1 : ℝ))) * (a * (a * (-1 : ℝ)))) ]), Real.sqrt_nonneg (a ^ 2 - a) ]
        nlinarith [ sq_nonneg (a * (a * (1 : ℝ))) ]
      · -- Assume a = 0
        have h4 : a = (0 : ℝ) := by nlinarith
        have h5 : (0 : ℝ) ∈ B := by
          rw [hB]
          simp [h4]
          all_goals nlinarith
        have h6 : (0 : ℝ) ∈ Ioc 0 3 := by
          apply h2
          exact h5
        norm_num at h6 ⊢
        all_goals try { tauto }
    have h32 : a ≤ 9 / 5 := by
      by_contra h4
      push_neg at h4
      have h6 : (a + Real.sqrt (a ^ 2 - a)) ∈ B := by
        rw [hB]
        simp
        nlinarith [ Real.sqrt_nonneg (a ^ 2 - a), Real.sq_sqrt (show (a ^ 2 - a) ≥ 0 by nlinarith [sq_nonneg (a * 10), sq_nonneg (a * (a - 1)), sq_nonneg (a * 2000)]), sq_nonneg (a * 10), sq_nonneg ((a) * (a * 5) ), sq_nonneg ((a) * (a * 0) + (a) * (a * 0) ) ]
      have h7 : (a + Real.sqrt (a ^ 2 - a)) ∈ Ioc 0 3 := by
        apply h2
        exact h6
      have h8 : (a + Real.sqrt (a ^ 2 - a)) ≤ (3 : ℝ) := by
        have h811 := h7.right
        try { tauto }
        <;> norm_num at h811 ⊢
        <;> nlinarith
      have h9 : (a + Real.sqrt (a ^ 2 - a)) > (3 : ℝ) := by
        nlinarith [ Real.sqrt_nonneg (a ^ 2 - a), Real.sq_sqrt (show (a ^ 2 - a) ≥ 0 by nlinarith), sq_nonneg (a), sq_nonneg (a * (a)), sq_nonneg (a * (a - 1) * (a - 1) ) ]
      linarith
    exact ⟨h31, h32⟩
  · -- Backward implication: From 0 < a ∧ a ≤ 9/5, prove (Ioc 0 3) ∪ B = Ioc 0 3
    rintro ⟨ha_pos, ha_le⟩
    ext x
    simp [hB, Set.mem_union, Set.mem_Ioc]
    intro h
    constructor
    · -- Show 0 < x
      by_contra h3
      push_neg at h3
      nlinarith [ sq_nonneg (x - a), sq_nonneg (x - (a + Real.sqrt (a ^ 2 - a)) ), sq_nonneg (x - (a - Real.sqrt (a ^ 2 - a)) ), Real.sqrt_nonneg (a ^ 2 - a), sq_nonneg ((x - 0) * (x - 0) * (x - 0) ), Real.sq_sqrt (show (a ^ 2 - a) ≥ 0 by nlinarith [sq_nonneg ((a - 0) * (a - 0) * (a - 1)), sq_nonneg ( (a - 0) ) ] ), sq_nonneg ((a - 9 / 5) * (a - 0) * (a - 10))
      ]
    · -- Show x ≤ 3
      by_contra h3
      push_neg at h3
      nlinarith [ sq_nonneg (x - a), sq_nonneg (x - 0), sq_nonneg (x * (x - 3) ), sq_nonneg (a * (a) ), sq_nonneg (a * (x - 3 * 1) ), sq_nonneg (a * ( (x ^ 2 - 0 ^ 2) ) ), sq_nonneg ( (a - 9 / 5) * (a - 0) * (a - 10) ), sq_nonneg (x - (a + Real.sqrt (a ^ 2 - a)) ), sq_nonneg (x - (a - Real.sqrt (a ^ 2 - a)) ), Real.sqrt_nonneg (a ^ 2 - a), Real.sq_sqrt (show (a ^ 2 - a) ≥ 0 by nlinarith [ sq_nonneg ((a - 0) * (a - 10) ), sq_nonneg ( (a * 5) - (2 * a) ) ]
      ), sq_nonneg (a * (a * 1 / 5) * (a * 1 / 5000) * (a * 1 / 5) * (a * 1 / 5) ) ]