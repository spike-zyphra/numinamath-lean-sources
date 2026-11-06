import Mathlib

open Real

theorem inequalities_319707 (x : ℝ) :
    ⌊x⌋ * (x - ⌊x⌋) < x - 1 ↔ x ≥ 2 := by
  constructor
  · -- Assume the inequality holds: prove x ≥ 2
    intro h
    by_contra h1
    push_neg at h1
    have h2 : ⌊x⌋ ≤ 1 := by
      by_contra h2
      push_neg at h2
      have h3 : ⌊x⌋ ≥ 2 := by omega
      have h4 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h3
      have h5 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
      nlinarith
    have h3 : ⌊x⌋ ≤ 1 := h2
    have h4 : ⌊x⌋ ≥ -1 := by
      by_contra h4
      push_neg at h4
      have h5 : ⌊x⌋ ≤ -2 := by omega
      have h5' : (⌊x⌋ : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h5
      have h6 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
      have h7 : (⌊x⌋ + 1 : ℝ) = (-1 : ℝ) := by 
        have h5' : (⌊x⌋ : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h5
        nlinarith
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x]
    have h7 : ⌊x⌋ = -1 ∨ ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 := by 
      omega
    rcases h7 with (h7 | h7 | h7)
    · -- ⌊x⌋ = -1
      have h8 : ⌊x⌋ = -1 := h7
      have h9 : (⌊x⌋ : ℝ) = (-1 : ℝ) := by exact_mod_cast h8
      rw [h9] at h
      have h10 : -1 ≤ (x : ℝ) := by 
        have h2 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
        rw [h9] at h2
        nlinarith
      have h11 : (x : ℝ) < (0 : ℝ) := by 
        have h5 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
        have h6 : (⌊x⌋ + 1 : ℝ) = (0 : ℝ) := by 
          rw [show (⌊x⌋ : ℝ) = (-1 : ℝ) by exact_mod_cast h8]
          norm_num
        linarith [h5, h6]
      nlinarith
    · -- ⌊x⌋ = 0
      have h8 : ⌊x⌋ = 0 := h7
      have h9 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h8
      rw [h9] at h
      have h10 : (0 : ℝ) ≤ x := by 
        have h2 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
        rw [h9] at h2
        nlinarith
      have h11 : (x : ℝ) < (1 : ℝ) := by 
        have h5 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
        have h6 : (⌊x⌋ + 1 : ℝ) = (1 : ℝ) := by 
          rw [show (⌊x⌋ : ℝ) = (0 : ℝ) by exact_mod_cast h8]
          norm_num
        linarith [h5, h6]
      nlinarith
    · -- ⌊x⌋ = 1
      have h8 : ⌊x⌋ = 1 := h7
      have h9 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h8
      rw [h9] at h
      have h10 : (1 : ℝ) ≤ x := by 
        have h2 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
        rw [h9] at h2
        nlinarith
      have h11 : (x : ℝ) < (2 : ℝ) := by 
        have h5 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
        have h6 : (⌊x⌋ + 1 : ℝ) = (2 : ℝ) := by 
          rw [show (⌊x⌋ : ℝ) = (1 : ℝ) by exact_mod_cast h8]
          norm_num
        linarith [h5, h6]
      nlinarith
  · -- Assume x ≥ 2:
    intro h
    have h4 : ⌊x⌋ ≥ 2 := by
      by_contra h4
      push_neg at h4
      have h5 : ⌊x⌋ ≤ 1 := by omega
      have h6 : (⌊x⌋ : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h5
      have h7 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
      have h8 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
      nlinarith
    have h5 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h4
    have h6 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
    have h7 : x - (⌊x⌋ : ℝ) < (1 : ℝ) := by
      have h8 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
      linarith
    nlinarith [Int.floor_le x, Int.lt_floor_add_one x]