import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_169059 :
  {x : ℤ | abs x < 3 * π}.ncard = 19 := by
  have h1 : {x : ℤ | abs x < 3 * π} = Set.Icc (-9 : ℤ) 9 := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor 
    · -- First prove the forward direction: if |x| < 3 * π, then x ∈ Icc (-9 : ℤ) 9
      intro h 
      -- Convert the inequality to the integer bound
      have h2 : abs x ≤ 9 := by 
        by_contra h2 
        push_neg at h2 
        have h3 : abs x ≥ 10 := by 
          omega 
        have h4 : abs x < (3 * π : ℝ) := by
          simpa using h 
        have h5 : abs x ≥ (10 : ℝ) := by 
          exact_mod_cast h3 
        have h6 : (3 * π : ℝ) < (10 : ℝ) := by 
          nlinarith [Real.pi_lt_31416]
        linarith 
      have h3 : x ≤ 9 := by 
        cases' abs_cases x with h4 h4 
        · -- Case x ≥ 0: abs x = x 
          omega 
        · -- Case x < 0: abs x = -x 
          omega 
      have h4 : x ≥ -9 := by 
        cases' abs_cases x with h5 h5 
        · -- Case x ≥ 0: abs x = x 
          omega 
        · -- Case x < 0: abs x = -x 
          omega 
      exact ⟨h4, h3⟩ 
    · -- Second prove the reverse direction: if x ∈ Icc (-9 : ℤ) 9, then |x| < 3 * π
      rintro ⟨h1, h2⟩ 
      have h3 : abs x ≤ 9 := by 
        cases' abs_cases x with h4 h4 
        · -- Case x ≥ 0: abs x = x 
          omega 
        · -- Case x < 0: abs x = -x 
          omega 
      have h4 : abs x < (3 * π : ℝ) := by 
        have h6 : abs x ≤ (9 : ℝ) := by 
          exact_mod_cast h3 
        -- Show 9 < 3 * π
        have h7 : abs x < (3 * π : ℝ) := by 
          have h8 : (9 : ℝ) < (3 * π : ℝ) := by 
            linarith [Real.pi_gt_31415] 
          linarith 
        simpa using h7 
      simpa using h4 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide