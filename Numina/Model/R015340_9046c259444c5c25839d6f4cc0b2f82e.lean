import Mathlib

theorem number_theory_107264 (x : ℝ) :
    ⌊x + 1 / 2⌋ + ⌊x + 1 / 3⌋ = 1 ↔ x ∈ Set.Ico (1 / 2) (2 / 3) := by
  constructor
  · -- Forward: if the sum of the floor expressions is 1, then x is in the interval [1/2, 2/3)
    intro h
    have h1 : ⌊x + 1 / 2⌋ + ⌊x + 1 / 3⌋ = 1 := h
    have h2 : ⌊x + 1 / 2⌋ = 1 - ⌊x + 1 / 3⌋ := by linarith 
    have h3 : ⌊x + 1 / 3⌋ ≤ (x + 1 / 3 : ℝ) := by exact Int.floor_le (x + 1 / 3)
    have h4 : (x + 1 / 3 : ℝ) < (⌊x + 1 / 3⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (x + 1 / 3)
    have h5 : ⌊x + 1 / 2⌋ ≤ (x + 1 / 2 : ℝ) := by exact Int.floor_le (x + 1 / 2)
    have h6 : (x + 1 / 2 : ℝ) < (⌊x + 1 / 2⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (x + 1 / 2)
    have h7 : ⌊x + 1 / 3⌋ = 0 ∨ ⌊x + 1 / 3⌋ = 1 := by
      have h8 : ⌊x + 1 / 3⌋ ≤ 1 := by 
        by_contra h9
        push_neg at h9
        have h10 : ⌊x + 1 / 3⌋ ≥ 2 := by omega 
        have h11 : ⌊x + 1 / 2⌋ ≤ -1 := by
          omega 
        have h11' : (⌊x + 1 / 2⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h11 
        have h17 : (⌊x + 1 / 3⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast (show ⌊x + 1 / 3⌋ ≥ 2 by omega)
        exfalso 
        nlinarith
      have h9 : ⌊x + 1 / 3⌋ ≥ 0 := by
        by_contra h10
        push_neg at h10
        have h11 : ⌊x + 1 / 3⌋ ≤ -1 := by omega 
        have h12 : ⌊x + 1 / 2⌋ ≥ 2 := by
          omega 
        have h12' : (⌊x + 1 / 2⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h12
        have h17 : (⌊x + 1 / 3⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast (show ⌊x + 1 / 3⌋ ≤ -1 by omega)
        exfalso 
        nlinarith 
      omega 
    rcases h7 with (h7 | h7) 
    · -- Assume ⌊x + 1 / 3⌋ = 0
      have h8 : ⌊x + 1 / 3⌋ = 0 := h7
      have h9 : ⌊x + 1 / 2⌋ = 1 := by 
        omega 
      constructor 
      · -- Show 1/2 ≤ x 
        have h10 : (0 : ℝ) ≤ x + 1 / 3 := by
          have h11 : ⌊x + 1 / 3⌋ ≤ (x + 1 / 3 : ℝ) := by exact Int.floor_le (x + 1 / 3)
          have h12 : (⌊x + 1 / 3⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h8 
          nlinarith 
        have h11 : (1 : ℝ) ≤ x + 1 / 2 := by
          have h12 : ⌊x + 1 / 2⌋ ≤ (x + 1 / 2 : ℝ) := by exact Int.floor_le (x + 1 / 2)
          have h13 : (⌊x + 1 / 2⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h9 
          nlinarith 
        nlinarith 
      · -- Show x < 2/3 
        have h12 : x + 1 / 3 < (1 : ℝ) := by
          have h11 : (x + 1 / 3 : ℝ) < (⌊x + 1 / 3⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (x + 1 / 3)
          have h12 : (⌊x + 1 / 3⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h8 
          nlinarith 
        nlinarith 
    · -- Case m = 1 
      have h8 : ⌊x + 1 / 3⌋ = 1 := h7 
      have h9 : ⌊x + 1 / 2⌋ = 0 := by 
        omega 
      -- Derive specific bounds
      have h10 : (1 : ℝ) ≤ x + 1 / 3 := by 
        have h11 : ⌊x + 1 / 3⌋ ≤ (x + 1 / 3 : ℝ) := by exact Int.floor_le (x + 1 / 3)
        have h12 : (⌊x + 1 / 3⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h8 
        nlinarith 
      have h11 : (x + 1 / 3 : ℝ) < (2 : ℝ) := by 
        have h12 : (x + 1 / 3 : ℝ) < (⌊x + 1 / 3⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (x + 1 / 3)
        have h13 : (⌊x + 1 / 3⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h8 
        nlinarith 
      have h12 : (0 : ℝ) ≤ x + 1 / 2 := by 
        have h13 : ⌊x + 1 / 2⌋ ≤ (x + 1 / 2 : ℝ) := by exact Int.floor_le (x + 1 / 2)
        have h14 : (⌊x + 1 / 2⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h9 
        nlinarith 
      have h13 : (x + 1 / 2 : ℝ) < (1 : ℝ) := by 
        have h14 : (x + 1 / 2 : ℝ) < (⌊x + 1 / 2⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (x + 1 / 2)
        have h15 : (⌊x + 1 / 2⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h9 
        nlinarith 
      -- Show contradiction of the bounds
      exfalso 
      linarith 
  · -- Backward: if x ∈ [1/2, 2/3), then the sum of the floor expressions is 1
    intro h 
    rcases h with ⟨h1, h2⟩ 
    have h3 : ⌊x + 1 / 2⌋ = 1 := by
      have h4 : 1 ≤ (x + 1 / 2 : ℝ) := by 
        nlinarith 
      have h5 : (x + 1 / 2 : ℝ) < (2 : ℝ) := by
        nlinarith 
      have h6 : ⌊x + 1 / 2⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try linarith) 
      linarith
    have h7 : ⌊x + 1 / 3⌋ = 0 := by 
      have h8 : 0 ≤ (x + 1 / 3 : ℝ) := by 
        nlinarith 
      have h9 : (x + 1 / 3 : ℝ) < (1 : ℝ) := by 
        nlinarith 
      have h10 : ⌊x + 1 / 3⌋ = 0 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try linarith) 
      linarith 
    linarith [h3, h7]