import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_6822 : {x : ℤ | abs x < 3 * π}.ncard = 19 := by
  have h1 : {x : ℤ | abs x < 3 * π} = Set.Icc (-9 : ℤ) 9 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First direction: abs x < 3 * π implies -9 ≤ x ∧ x ≤ 9
      intro h
      have h6 : abs x < 10 := by
        by_contra h3
        push_neg at h3
        have h3' : abs x ≥ 10 := by
          omega
        have h9 : (abs x : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h3'
        have h10 : (abs x : ℝ) < (3 * Real.pi : ℝ) := by
          simpa using h
        nlinarith [abs_nonneg x, Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
      constructor
      · -- Show that -9 ≤ x
        cases' abs_cases x with h1 h1
        · -- Assume x >= 0
          omega
        · -- Assume x < 0
          omega
      · -- Show that x ≤ 9
        cases' abs_cases x with h1 h1
        · -- Assume x >= 0
          omega
        · -- Assume x < 0
          omega
    · -- Second direction: (-9 ≤ x ∧ x ≤ 9) implies abs x < 3 * π
      rintro ⟨h1, h2⟩
      have h8 : abs x ≤ 9 := by
        cases' abs_cases x with h h
        · linarith 
        · linarith 
      have h10 : abs x < (3 * Real.pi : ℝ) := by 
        have h13 : abs x ≤ 9 := h8 
        have h14 : (abs x : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h13 
        have h15 : (abs x : ℝ) < (3 * Real.pi : ℝ) := by 
          have h14' : (abs x : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h13 
          nlinarith [Real.pi_gt_31415, abs_nonneg x] 
        simpa using h15 
      simpa using h10 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide