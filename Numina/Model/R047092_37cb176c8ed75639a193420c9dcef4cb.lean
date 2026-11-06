import Mathlib

open Real

theorem algebra_93841 (n : ℕ) (hn : 1 ≤ n) :
    arctan (1 / 3) + arctan (1 / 4) + arctan (1 / 5) + arctan (1 / n) = π / 4 ↔ n = 47 := by
  constructor
  · -- Assume the equation holds, prove n = 47.
    intro h_eq
    have h1 : n ≥ 1 := by linarith
    have eq1 : (n : ℝ) ≥ 1 := by exact_mod_cast h1
    have h2 : arctan (1 / 3) + arctan (1 / 4) = arctan (7 / 11) := by
      rw [arctan_add]
      norm_num
      all_goals norm_num
    have h3 : arctan (7 / 11) + arctan (1 / 5) = arctan (23 / 24) := by
      rw [arctan_add]
      norm_num
      all_goals norm_num
    have eq2 : arctan (23 / 24) + arctan (1 / n) = π / 4 := by
      have h4 : arctan (1 / 3) + arctan (1 / 4) = arctan (7 / 11) := h2
      have h5 : arctan (7 / 11) + arctan (1 / 5) = arctan (23 / 24) := h3
      linarith [h_eq, h4, h5]
    have eq3 : arctan (1 / n) = π / 4 - arctan (23 / 24) := by linarith
    have eq4 : (n : ℝ) = 47 := by
      have eq5 : arctan (1 / n) = arctan (1 / 47) := by
        rw [eq3]
        have h1 : arctan (1 / 47) = π / 4 - arctan (23 / 24) := by
          have h5 : arctan (1 / 47) + arctan (23 / 24) = π / 4 := by
            have h7 : arctan (1 / 47) + arctan (23 / 24) = π / 4 := by
              rw [arctan_add]
              norm_num
              all_goals norm_num [arctan_one]
            linarith
          linarith
        linarith
      have eq10 : arctan (1 / n) = arctan (1 / 47) := eq5
      have eq11 : (1 / n : ℝ) = (1 / 47 : ℝ) := by
        apply Real.arctan_injective
        linarith [eq10]
      have eq12 : (n : ℝ) = (47 : ℝ) := by
        field_simp at eq11 ⊢
        nlinarith
      nlinarith
    have h32 : n = 47 := by
      exact_mod_cast eq4
    exact_mod_cast h32
  · -- Assume n = 47, prove the equation holds
    intro heq
    rw [heq]
    have h2 : arctan (1 / 3) + arctan (1 / 4) = arctan (7 / 11) := by
      rw [arctan_add]
      norm_num
      all_goals norm_num
    have h3 : arctan (7 / 11) + arctan (1 / 5) = arctan (23 / 24) := by
      rw [arctan_add]
      norm_num
      all_goals norm_num
    have h6 : arctan (23 / 24) + arctan (1 / 47) = π / 4 := by
      rw [arctan_add]
      norm_num
      all_goals norm_num [arctan_one]
    linarith [h2, h3, h6]