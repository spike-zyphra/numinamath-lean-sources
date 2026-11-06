import Mathlib 
open Real

theorem algebra_660 : {z : ℝ | z ≥ 0 ∧ (2 * √z - 3) / (√z - 1) - 1 = (3 * √z - 1) / (1 - √z)} = {9 / 16} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume z is in the left side
    intro h
    rcases h with ⟨hz1, heq⟩
    have h1 : √z ≥ 0 := by positivity
    by_cases h3 : √z - 1 = 0
    · -- If √z - 1 = 0, then √z = 1
      have h4 : √z = 1 := by linarith
      have h5 : z = 1 := by
        calc
          z = (√z) ^ 2 := by rw [Real.sq_sqrt]; all_goals nlinarith
          _ = 1 ^ 2 := by rw [h4]
          _ = 1 := by norm_num
      rw [h4] at heq
      norm_num [h4] at heq
      all_goals nlinarith
    · -- √z - 1 ≠ 0
      have h4 : √z - 1 ≠ 0 := h3
      have h6 : (1 - √z : ℝ) ≠ 0 := by
        intro h7
        have : √z = 1 := by linarith
        have : √z - 1 = 0 := by linarith
        contradiction
      have h7 : (2 * √z - 3) / (√z - 1) - 1 = (3 * √z - 1) / (1 - √z) := by
        linarith [heq]
      -- Simplify RHS
      have h8 : (3 * √z - 1) / (1 - √z) = - (3 * √z - 1) / (√z - 1) := by
        have h11 : 1 - √z ≠ 0 := h6
        have h12 : √z - 1 ≠ 0 := h4
        have h9 : (1 - √z : ℝ) = - (√z - 1 : ℝ) := by
          linarith
        rw [h9]
        rw [div_neg]
        <;> ring
      have eq1 : (2 * √z - 3) / (√z - 1) - 1 = - (3 * √z - 1) / (√z - 1) := by 
        rw [h8] at h7
        linarith
      have eq2 : √z - 2 = - (3 * √z - 1) := by
        have h11 : √z - 1 ≠ 0 := h4
        have h14 : (2 * √z - 3) / (√z - 1) - 1 = - (3 * √z - 1) / (√z - 1) := eq1
        have eq3 : (2 * √z - 3) / (√z - 1) - 1 = (√z - 2) / (√z - 1) := by
          field_simp [(show √z - 1 ≠ 0 by assumption)]
          <;> nlinarith
        rw [eq3] at h14
        have eq4 : (√z - 2) = - (3 * √z - 1) := by 
          field_simp [(show √z - 1 ≠ 0 by assumption)] at h14 ⊢
          <;> nlinarith
        exact_mod_cast eq4
      have h10 : 4 * √z = 3 := by
        nlinarith
      have h11 : √z = 3 / 4 := by
        nlinarith
      have h12 : z = 9 / 16 := by
        calc
          z = (√z) ^ 2 := by rw [Real.sq_sqrt]; all_goals nlinarith
          _ = (3 / 4) ^ 2 := by rw [h11]
          _ = (9 / 16) := by norm_num
      linarith
  · -- Show the reverse direction
    intro h_eq
    constructor
    · -- Show z ≥ 0
      rw [h_eq]
      norm_num
    · -- Show the equation holds
      rw [h_eq]
      have h1 : √(9 / 16 : ℝ) = 3 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num