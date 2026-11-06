import Mathlib

theorem inequalities_124626 (A : ℕ) (hA : A > 0) :
    (5 / 9 : ℚ) < (9 / A : ℚ) ∧ (9 / A : ℚ) < 1 ↔
    A = 10 ∨ A = 11 ∨ A = 12 ∨ A = 13 ∨ A = 14 ∨ A = 15 ∨ A = 16 := by
  constructor
  · -- Forward: If the inequalities hold, then A is in the set.
    intro h
    rcases h with ⟨h1, h2⟩
    have h4 : (9 : ℚ) / (A : ℚ) < (1 : ℚ) := by
      linarith [h2]
    have h5 : (5 / 9 : ℚ) < (9 / (A : ℚ)) := by
      linarith [h1]
    have hA1 : A > 9 := by
      by_contra h
      push_neg at h
      have : A ≤ 9 := by linarith
      have h6 : (A : ℚ) ≤ (9 : ℚ) := by exact_mod_cast this
      have h7 : (9 : ℚ) / (A : ℚ) ≥ (1 : ℚ) := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [h6]
      linarith [h4, h7]
    have hA2 : A < 17 := by
      by_contra h
      push_neg at h
      have : A ≥ 17 := by linarith
      have h8 : (A : ℚ) ≥ (17 : ℚ) := by exact_mod_cast this
      have h9 : (5 / 9 : ℚ) ≥ (9 / (A : ℚ)) := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h8]
      linarith [h5, h9]
    have : A = 10 ∨ A = 11 ∨ A = 12 ∨ A = 13 ∨ A = 14 ∨ A = 15 ∨ A = 16 := by
      omega
    assumption
  · -- Backward: If A is in the set, then the inequalities hold.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- A = 10
      constructor
      · norm_num
      · norm_num
    · -- A = 11
      constructor
      · norm_num
      · norm_num
    · -- A = 12
      constructor
      · norm_num
      · norm_num
    · -- A = 13
      constructor
      · norm_num
      · norm_num
    · -- A = 14
      constructor
      · norm_num
      · norm_num
    · -- A = 15
      constructor
      · norm_num
      · norm_num
    · -- A = 16
      constructor
      · norm_num
      · norm_num