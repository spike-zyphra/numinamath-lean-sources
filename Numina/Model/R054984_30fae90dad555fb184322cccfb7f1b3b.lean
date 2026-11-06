import Mathlib

theorem number_theory_199357 (x : ℝ) :
    x > 0 ∧ x < 7 ∧ ⌊x * ⌊x * ⌊x⌋⌋⌋ < 2018 ↔
    x ∈ Set.Ioo 0 7 := by
  constructor
  · -- Forward direction: (x > 0 ∧ x < 7 ∧ ⌊x * ⌊x * ⌊x⌋⌋⌋ < 2018) → x ∈ Set.Ioo 0 7
    rintro ⟨hx1, hx2, h3⟩
    exact ⟨hx1, hx2⟩
  · -- Reverse direction: x ∈ Set.Ioo 0 7 → (x > 0 ∧ x < 7 ∧ ⌊x * ⌊x * ⌊x⌋⌋⌋ < 2018)
    rintro ⟨hx1, hx2⟩
    have h1 : ⌊x⌋ ≤ 6 := by
      by_contra h'
      push_neg at h'
      have h3 : ⌊x⌋ ≥ 7 := by omega
      have h4 : (⌊x⌋ : ℝ) ≥ 7 := by exact_mod_cast h3
      have h5 : x ≥ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_le x
      linarith [hx2, h4, h5]
    have h2 : ⌊x * ⌊x⌋⌋ ≤ 41 := by
      have h3 : x < 7 := by linarith [hx2]
      have h4 : (⌊x⌋ : ℝ) ≤ 6 := by exact_mod_cast (show ⌊x⌋ ≤ 6 by omega)
      have h6 : x * (⌊x⌋ : ℝ) < 42 := by
        nlinarith [h3, h4]
      have h7 : ⌊x * ⌊x⌋⌋ ≤ 41 := by
        by_contra h8
        push_neg at h8
        have h9 : ⌊x * ⌊x⌋⌋ ≥ 42 := by omega
        have h10 : (⌊x * ⌊x⌋⌋ : ℝ) ≥ 42 := by exact_mod_cast h9
        have h11 : (⌊x * ⌊x⌋⌋ : ℝ) ≤ x * (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_le (x * (⌊x⌋ : ℝ))
        linarith [h6, h11, h10]
      omega
    have h3 : ⌊x * ⌊x * ⌊x⌋⌋⌋ ≤ 342 := by
      have h4 : x < 7 := by linarith [hx2]
      have h5 : (⌊x * ⌊x⌋⌋ : ℝ) ≤ 41 := by exact_mod_cast (show ⌊x * ⌊x⌋⌋ ≤ 41 by omega)
      have h6 : x * (⌊x * ⌊x⌋⌋ : ℝ) < 287 := by
        nlinarith [h4, h5]
      have h7 : ⌊x * ⌊x * ⌊x⌋⌋⌋ ≤ 342 := by
        by_contra h8
        push_neg at h8
        have h9 : ⌊x * ⌊x * ⌊x⌋⌋⌋ ≥ 343 := by omega
        have h10 : (⌊x * ⌊x * ⌊x⌋⌋⌋ : ℝ) ≥ 343 := by exact_mod_cast h9
        have h11 : (⌊x * ⌊x * ⌊x⌋⌋⌋ : ℝ) ≤ x * (⌊x * ⌊x⌋⌋ : ℝ) := by exact_mod_cast Int.floor_le (x * (⌊x * ⌊x⌋⌋ : ℝ))
        linarith [h6, h11, h10]
      omega
    constructor
    · linarith
    constructor
    · linarith
    · omega