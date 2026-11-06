import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_17033 : Set.ncard {c : ℝ | abs (1 / 2 - c * I) = 3 / 4} = 2 := by
  have h : {c : ℝ | abs (1 / 2 - c * I) = 3 / 4} = {Real.sqrt 5 / 4, -Real.sqrt 5 / 4} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    have h_abs : abs (1 / 2 - c * I) = Real.sqrt ((1 / 2 : ℝ) ^ 2 + (c : ℝ) ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      ring
    rw [h_abs]
    constructor
    · intro h1
      have h2 : (Real.sqrt ((1 / 2 : ℝ) ^ 2 + (c : ℝ) ^ 2)) = (3 / 4 : ℝ) := by
        linarith
      have h3 : (1 / 2 : ℝ) ^ 2 + (c : ℝ) ^ 2 = (9 / 16 : ℝ) := by
        calc
          (1 / 2 : ℝ) ^ 2 + (c : ℝ) ^ 2 = (Real.sqrt ((1 / 2 : ℝ) ^ 2 + (c : ℝ) ^ 2)) ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          _ = (3 / 4 : ℝ) ^ 2 := by
            rw [h2]
          _ = (9 / 16 : ℝ) := by norm_num
      have h4 : (c : ℝ) ^ 2 = (5 / 16 : ℝ) := by
        nlinarith
      have h5 : (c - Real.sqrt 5 / 4) * (c + Real.sqrt 5 / 4) = 0 := by
        ring_nf
        have h6 : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
          simp [Real.sq_sqrt]
          all_goals linarith
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), h6]
      cases' (mul_eq_zero.mp h5) with h7 h8
      · left
        linarith
      · right
        linarith
    · rintro (h | h)
      · rw [h]
        have h5 : Real.sqrt ((1 / 2 : ℝ) ^ 2 + (Real.sqrt 5 / 4 : ℝ) ^ 2) = (3 / 4 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [Real.sq_sqrt] <;> ring_nf <;> norm_num
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        rw [h5]
      · rw [h]
        have h5 : Real.sqrt ((1 / 2 : ℝ) ^ 2 + (-Real.sqrt 5 / 4 : ℝ) ^ 2) = (3 / 4 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [Real.sq_sqrt] <;> ring_nf <;> norm_num
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        rw [h5]
  rw [h]
  apply Set.ncard_pair
  intro h
  have h1 : Real.sqrt 5 = 0 := by
    linarith
  have h3 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  linarith