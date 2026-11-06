import Mathlib

theorem algebra_193293 (x : ℝ) :
    ⌊x - 1⌋ = ⌊(x + 2) / 2⌋ ↔ 3 ≤ x ∧ x < 5 := by
  constructor
  · -- Assume the equation holds, prove 3 ≤ x ∧ x < 5
    intro h_eq
    set n := ⌊x - 1⌋ with hn1
    have h_eq' : ⌊(x + 2) / 2⌋ = n := by 
      omega
    have h1 : (n : ℝ) ≤ x - 1 := by 
      have h3 : (⌊x - 1⌋ : ℝ) ≤ x - 1 := by 
        exact Int.floor_le (x - 1)
      have hn : (⌊x - 1⌋ : ℝ) = (n : ℝ) := by 
        exact_mod_cast hn1
      nlinarith
    have h2 : x - 1 < (n + 1 : ℝ) := by 
      have h4 : x - 1 < (⌊x - 1⌋ + 1 : ℝ) := by 
        exact Int.lt_floor_add_one (x - 1)
      have hn : (⌊x - 1⌋ : ℝ) = (n : ℝ) := by 
        exact_mod_cast hn1
      nlinarith
    have h3' : (n : ℝ) ≤ (x + 2) / 2 := by 
      have h5 : (⌊(x + 2) / 2⌋ : ℝ) ≤ (x + 2) / 2 := by 
        exact Int.floor_le ((x + 2) / 2)
      have hn' : (⌊(x + 2) / 2⌋ : ℝ) = (n : ℝ) := by 
        exact_mod_cast h_eq'
      nlinarith
    have h4' : (x + 2) / 2 < (n + 1 : ℝ) := by 
      have h6 : (x + 2) / 2 < (⌊(x + 2) / 2⌋ + 1 : ℝ) := by 
        exact Int.lt_floor_add_one ((x + 2) / 2)
      have hn' : (⌊(x + 2) / 2⌋ : ℝ) = (n : ℝ) := by 
        exact_mod_cast h_eq'
      nlinarith
    have h5 : n ≥ 2 := by 
      by_contra h
      push_neg at h
      have : n ≤ 1 := by omega
      have hnle1 : (n : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast this
      nlinarith [Int.floor_le (x - 1), Int.floor_le ((x + 2) / 2), 
          Int.lt_floor_add_one (x - 1), Int.lt_floor_add_one ((x + 2) / 2)]
    have h6 : n ≤ 3 := by 
      by_contra h
      push_neg at h
      have : n ≥ 4 := by omega
      have hnge4 : (n : ℝ) ≥ (4 : ℝ) := by
        exact_mod_cast this
      nlinarith [Int.floor_le (x - 1), Int.floor_le ((x + 2) / 2), 
          Int.lt_floor_add_one (x - 1), Int.lt_floor_add_one ((x + 2) / 2)]
    have h7 : n = 2 ∨ n = 3 := by 
      omega
    rcases h7 with (r | r)
    · -- Case n = 2
      have hn2' : (n : ℝ) = (2 : ℝ) := by 
        exact_mod_cast r
      have h8 : (3 : ℝ) ≤ x := by 
        nlinarith
      have h9 : x < (5 : ℝ) := by
        nlinarith
      constructor <;> linarith
    · -- Case n = 3
      have hn2' : (n : ℝ) = (3 : ℝ) := by 
        exact_mod_cast r
      have h8 : (3 : ℝ) ≤ x := by 
        nlinarith
      have h9 : x < (5 : ℝ) := by
        nlinarith
      constructor <;> linarith
  · -- Now the reverse, given the interval, prove the equation holds
    rintro ⟨h1, h2⟩
    by_cases h4 : x < (4 : ℝ)
    · -- Case x ∈ [3,4)
      have h5 : ⌊x - 1⌋ = 2 := by 
        have h6 : 2 ≤ (x - 1 : ℝ) := by 
          nlinarith
        have h7 : x - 1 < (3 : ℝ) := by 
          nlinarith
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      have h8 : ⌊(x + 2) / 2⌋ = 2 := by
        have h9 : 2.5 ≤ (x + 2) / 2 := by
          nlinarith
        have h10 : (x + 2) / 2 < (3.5 : ℝ) := by
          nlinarith
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      omega
    · -- Case 4 ≤x <5
      have h5 : ⌊x - 1⌋ = 3 := by 
        have h6 : 3 ≤ (x - 1 : ℝ) := by 
          nlinarith
        have h7 : x - 1 < (4 : ℝ) := by 
          nlinarith
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      have h8 : ⌊(x + 2) / 2⌋ = 3 := by
        have h9 : 2.5 ≤ (x + 2) / 2 := by
          nlinarith
        have h10 : (x + 2) / 2 < (3.5 : ℝ) := by
          nlinarith
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      omega