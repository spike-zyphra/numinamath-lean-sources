import Mathlib


theorem algebra_9303 (x : ℝ) :
⌊x⌋ ^ 2 - 5 * ⌊x⌋ - 36 ≤ 0 ↔ -4 ≤ x ∧ x < 10 := by
  constructor
  · -- Prove the forward direction
    intro h
    have h1 : -4 ≤ (⌊x⌋ : ℤ) := by
      nlinarith
    have h2 : (⌊x⌋ : ℤ) ≤ 9 := by
      nlinarith
    constructor
    · -- Show that -4 ≤ x
      have h3 : -4 ≤ x := by
        have h4 : (⌊x⌋ : ℝ) ≤ x := by
          exact Int.floor_le x
        have h8 : (⌊x⌋ : ℝ) ≥ (-4 : ℝ) := by
          exact_mod_cast h1
        nlinarith
      linarith
    · -- Show that x < 10
      have h8 : x < (10 : ℝ) := by
        have h7 : x < (⌊x⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one x
        have h9 : (⌊x⌋ : ℝ) ≤ (9 : ℝ) := by
          have h10 : (⌊x⌋ : ℤ) ≤ 9 := h2
          exact_mod_cast h10
        nlinarith
      linarith
  · -- Prove the reverse direction
    rintro ⟨h1, h2⟩
    have h3 : -4 ≤ (⌊x⌋ : ℤ) := by
      by_contra h
      push_neg at h
      have h10 : ⌊x⌋ ≤ (-5 : ℤ) := by
        omega
      have h11 : (⌊x⌋ : ℝ) ≤ (-5 : ℝ) := by
        exact_mod_cast h10
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x, h11]
    have h4 : (⌊x⌋ : ℤ) ≤ 9 := by
      by_contra h
      push_neg at h
      have h10 : ⌊x⌋ ≥ 10 := by
        omega
      have h11 : (⌊x⌋ : ℝ) ≥ (10 : ℝ) := by
        exact_mod_cast h10
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x, h11]
    nlinarith