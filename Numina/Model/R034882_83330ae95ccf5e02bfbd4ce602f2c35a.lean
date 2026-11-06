import Mathlib

theorem inequalities_626745 :
    Set.ncard {x : ℤ | -6 < (8 - 2 * (Int.cast x : ℝ)) / 8 ∧ (8 - 2 * (Int.cast x : ℝ)) / 8 ≤ 4} = 40 := by
  have h1 : {x : ℤ | -6 < (8 - 2 * (Int.cast x : ℝ)) / 8 ∧ (8 - 2 * (Int.cast x : ℝ)) / 8 ≤ 4} = Set.Icc (-12 : ℤ) 27 := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor 
    · -- Forward: If x satisfies the inequality then x ∈ [-12, 27]
      rintro ⟨h₁, h₂⟩
      have h11 : (x : ℝ) < 28 := by 
        have h6 : (8 - 2 * (x : ℝ)) / 8 > -6 := by linarith [h₁]
        have h7 : (8 - 2 * (x : ℝ)) > -48 := by
          linarith 
        nlinarith 
      have h12 : (x : ℝ) ≥ -12 := by 
        have h6 : (8 - 2 * (x : ℝ)) / 8 ≤ 4 := by linarith [h₂]
        have h7 : (8 - 2 * (x : ℝ)) ≤ 32 := by
          linarith 
        nlinarith 
      have hx1 : x < 28 := by 
        by_contra h 
        push_neg at h 
        have h3 : x ≥ 28 := by omega 
        have h4 : (x : ℝ) ≥ (28 : ℝ) := by exact_mod_cast h3 
        nlinarith -- contradiction 
      have hx2 : x ≥ -12 := by 
        by_contra h 
        push_neg at h 
        have h3 : x ≤ -13 := by omega 
        have h4 : (x : ℝ) ≤ (-13 : ℝ) := by exact_mod_cast h3 
        nlinarith -- contradiction 
      exact ⟨hx2, by omega⟩ 
    · -- Backward: If x ∈ [-12, 27] then x satisfies the inequality 
      rintro ⟨hx1, hx2⟩ 
      have h3 : (x : ℝ) < (28 : ℝ) := by exact_mod_cast show x < 28 by omega 
      have h4 : (x : ℝ) ≥ (-12 : ℝ) := by exact_mod_cast hx1 
      constructor 
      · -- First part: -6 < (8 - 2 * x) / 8 
        nlinarith 
      · -- Second part: (8 - 2 * x) / 8 ≤ 4 
        nlinarith 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide