import Mathlib

theorem algebra_11125 (x : ℝ) :
    2 * ⌊2 * x - 1⌋ ^ 2 + ⌊2 * x - 1⌋ - 1 = 0 ↔ x ∈ Set.Ico 0 (1 / 2) := by
  constructor
  · -- Assume 2 * ⌊2 * x - 1⌋ ^ 2 + ⌊2 * x - 1⌋ - 1 = 0, prove x ∈ Set.Ico 0 (1 / 2)
    intro h
    have h1 : ⌊2 * x - 1⌋ = -1 := by
      have h_eq : 2 * ⌊2 * x - 1⌋ ^ 2 + ⌊2 * x - 1⌋ - 1 = 0 := h
      have h4 : ⌊2 * x - 1⌋ = -1 := by
        ring_nf at h_eq
        have h5 : ⌊2 * x - 1⌋ ≤ 0 := by
          nlinarith [sq_nonneg ( ⌊2 * x - 1⌋ : ℤ ) ]
        have h7 : ⌊2 * x - 1⌋ ≥ -1 := by
          nlinarith [sq_nonneg ( ⌊2 * x - 1⌋ : ℤ ) ]
        interval_cases ( ⌊2 * x - 1⌋ : ℤ ) <;> try { tauto }
      exact h4
    have h2 : (⌊2 * x - 1⌋ : ℝ) = -1 := by
      exact_mod_cast h1
    have h3 : -1 ≤ 2 * x - 1 := by
      have h4 : (⌊2 * x - 1⌋ : ℝ) ≤ 2 * x - 1 := by
        exact Int.floor_le (2 * x - 1)
      rw [h2] at h4
      linarith
    have h4 : 2 * x - 1 < 0 := by
      have h5 : (2 * x - 1) < (⌊2 * x - 1⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (2 * x - 1)
      rw [h2] at h5
      linarith
    constructor
    · -- Show x ≥ 0
      nlinarith
    · -- Show x < 1 / 2
      nlinarith
  · -- Assume x ∈ Set.Ico 0 (1 / 2), prove 2 * ⌊2 * x - 1⌋ ^ 2 + ⌊2 * x - 1⌋ - 1 = 0
    rintro (⟨hx1, hx2⟩)
    have h1 : ⌊2 * x - 1⌋ = -1 := by
      have h2 : -1 ≤ 2 * x - 1 := by
        linarith
      have h3 : 2 * x - 1 < 0 := by
        linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
    rw [h1]
    all_goals norm_num