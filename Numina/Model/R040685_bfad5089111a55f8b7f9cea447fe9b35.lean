import Mathlib


open Real


lemma lemma_1 (x : ℝ) (h : -x^2 - 4 * x - 9 = -(x^2 + 5 * x + 6)) : x = 3 := by
  have h1 : -(x^2 + 5 * x + 6) = -x^2 - 5 * x - 6 := by
    ring
  rw [h1] at h
  nlinarith


theorem algebra_249035 :
    {x : ℝ | x ≠ -2 ∧ x ≠ -3 ∧ (3125 : ℝ) ^ ((x + 1) / (x + 2)) * (15625 : ℝ) ^ (-(x + 2) / (x + 3)) = 0.2} = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if x ∈ {x ∈ ℝ | x ≠ -2 ∧ x ≠ -3 ∧ (3125 : ℝ) ^ ((x + 1) / (x + 2)) * (15625 : ℝ) ^ (-(x + 2) / (x + 3)) = 0.2}, then x ∈ {3}
    intro h
    rcases h with ⟨hx1, hx2, heq⟩
    have h1 : (3125 : ℝ) ^ ((x + 1) / (x + 2)) = (5 : ℝ) ^ (5 * ((x + 1) / (x + 2) : ℝ)) := by
      rw [show (3125 : ℝ) = (5 : ℝ) ^ (5 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h2 : (15625 : ℝ) ^ (-(x + 2) / (x + 3)) = (5 : ℝ) ^ (6 * (-(x + 2) / (x + 3) : ℝ)) := by
      rw [show (15625 : ℝ) = (5 : ℝ) ^ (6 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h1, h2] at heq
    have h3 : 5 * ((x + 1) / (x + 2) : ℝ) + (6 * (-(x + 2) / (x + 3) : ℝ)) = -1 := by
      have h_eq1 : (5 : ℝ) ^ (5 * ((x + 1) / (x + 2) : ℝ) + (6 * (-(x + 2) / (x + 3) : ℝ)) ) = (5 : ℝ) ^ (-1 : ℝ) := by
        have h4 : (5 : ℝ) ^ (5 * ((x + 1) / (x + 2) : ℝ)) * (5 : ℝ) ^ (6 * (-(x + 2) / (x + 3) : ℝ)) = (5 : ℝ) ^ (5 * ((x + 1) / (x + 2) : ℝ) + (6 * (-(x + 2) / (x + 3) : ℝ)) ) := by
          rw [← Real.rpow_add]
          all_goals ring_nf
          all_goals nlinarith
        rw [h4] at heq
        have h5 : (0.2 : ℝ) = (5 : ℝ) ^ (-1 : ℝ) := by
          norm_num
        rw [h5] at heq
        linarith
      have h6 : 5 * ((x + 1) / (x + 2) : ℝ) + (6 * (-(x + 2) / (x + 3) : ℝ)) = -1 := by
        apply_fun (Real.logb (5 : ℝ)) at h_eq1
        have h7 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (-1 : ℝ)) = (-1 : ℝ) := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h8 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (5 * ((x + 1) / (x + 2) : ℝ) + (6 * (-(x + 2) / (x + 3) : ℝ)) )) = 5 * ((x + 1) / (x + 2) : ℝ) + (6 * (-(x + 2) / (x + 3) : ℝ)) := by
          rw [Real.logb_rpow]
          all_goals nlinarith
        rw [h8, h7] at h_eq1
        linarith
        all_goals nlinarith
      linarith
    have hx10 : x + 2 ≠ 0 := by
      intro h11
      apply hx1
      linarith
    have hx11 : x + 3 ≠ 0 := by
      intro h22
      apply hx2
      linarith
    field_simp [(show x + 2 ≠ 0 by intro h11; apply hx1; linarith), (show x + 3 ≠ 0 by intro h22; apply hx2; linarith)] at h3
    have hx_eq : x = 3 := by
      have hx12 : -x^2 - 4 * x - 9 = -(x^2 + 5 * x + 6) := by
        nlinarith
      apply lemma_1 x hx12
      <;> nlinarith
    linarith
  · -- Second direction: if x ∈ {3}, then x ∈ {x ∈ ℝ | x ≠ -2 ∧ x ≠ -3 ∧ (3125 : ℝ) ^ ((x + 1) / (x + 2)) * (15625 : ℝ) ^ (-(x + 2) / (x + 3)) = 0.2}
    intro h
    rw [h]
    constructor
    · -- Show x ≠ -2
      norm_num
    constructor
    · -- Show x ≠ -3
      norm_num
    · -- Show the equation holds
      have h1 : (3125 : ℝ) ^ ((3 + 1 : ℝ) / (3 + 2 : ℝ)) = (5 : ℝ) ^ (4 : ℝ) := by
        rw [show (3125 : ℝ) = (5 : ℝ) ^ (5 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h2 : (15625 : ℝ) ^ (-(3 + 2 : ℝ) / (3 + 3 : ℝ)) = (5 : ℝ) ^ (-5 : ℝ) := by
        rw [show (15625 : ℝ) = (5 : ℝ) ^ (6 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      rw [h1, h2]
      norm_num
      <;> ring_nf <;> norm_num