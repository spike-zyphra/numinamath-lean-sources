import Mathlib

theorem number_theory_309777 (n : ℕ) :
    n > 0 ∧
    ⌊(n / 2 : ℝ)⌋ + ⌊(n / 3 : ℝ)⌋ + ⌊(n / 4 : ℝ)⌋ + ⌊(n / 5 : ℝ)⌋ = 69 ↔ n = 55 := by
  constructor
  · -- Assume n > 0 ∧ ⌊(n / 2 : ℝ)⌋ + ... + ⌊(n / 5 : ℝ)⌋ = 69, prove n = 55
    intro h
    rcases h with ⟨hn_pos, heq⟩
    have h5 : n ≥ 1 := by
      omega
    have h1 : n ≤ 80 := by
      by_contra h
      push_neg at h
      have h9 : n ≥ 81 := by
        omega
      have h11 : ⌊(n / 2 : ℝ)⌋ ≥ 40 := by
        have h2 : (n : ℝ) ≥ (81 : ℝ) := by
          exact_mod_cast h9
        have h3 : (n / (2 : ℝ)) ≥ (40.5 : ℝ) := by
          nlinarith
        have h5 : ⌊(n / 2 : ℝ)⌋ ≥ 40 := by
          have h7 : ⌊(n / 2 : ℝ)⌋ ≥ ⌊(40.5 : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          have h8 : ⌊(40.5 : ℝ)⌋ = 40 := by
            norm_num
          omega
        linarith
      have h11 : ⌊(n / 3 : ℝ)⌋ ≥ 27 := by
        have h2 : (n : ℝ) ≥ (81 : ℝ) := by
          exact_mod_cast h9
        have h3 : (n / (3 : ℝ)) ≥ (27 : ℝ) := by
          nlinarith
        have h4 : ⌊(n / 3 : ℝ)⌋ ≥ 27 := by
          have h7 : ⌊(n / 3 : ℝ)⌋ ≥ ⌊(27 : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          have h8 : ⌊(27 : ℝ)⌋ = 27 := by
            norm_num
          omega
        linarith
      have h12 : ⌊(n / 4 : ℝ)⌋ ≥ 20 := by
        have h2 : (n : ℝ) ≥ (81 : ℝ) := by
          exact_mod_cast h9
        have h3 : (n / (4 : ℝ)) ≥ (20.25 : ℝ) := by
          nlinarith
        have h4 : ⌊(n / 4 : ℝ)⌋ ≥ 20 := by
          have h7 : ⌊(n / 4 : ℝ)⌋ ≥ ⌊(20.25 : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          have h8 : ⌊(20.25 : ℝ)⌋ = 20 := by
            norm_num
          omega
        linarith
      have h13 : ⌊(n / 5 : ℝ)⌋ ≥ 16 := by
        have h2 : (n : ℝ) ≥ (81 : ℝ) := by
          exact_mod_cast h9
        have h3 : (n / (5 : ℝ)) ≥ (16.2 : ℝ) := by
          nlinarith
        have h4 : ⌊(n / 5 : ℝ)⌋ ≥ 16 := by
          have h7 : ⌊(n / 5 : ℝ)⌋ ≥ ⌊(16.2 : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          have h8 : ⌊(16.2 : ℝ)⌋ = 16 := by
            norm_num
          omega
        linarith
      have heq : ⌊(n / 2 : ℝ)⌋ + ⌊(n / 3 : ℝ)⌋ + ⌊(n / 4 : ℝ)⌋ + ⌊(n / 5 : ℝ)⌋ = 69 := by
        linarith [heq]
      omega
    interval_cases n <;> norm_num [Int.floor_eq_iff] at heq ⊢ <;> omega
  · -- Assume n = 55, prove n > 0 ∧ equ
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num [Int.floor_eq_iff]