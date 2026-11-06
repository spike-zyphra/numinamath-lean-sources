import Mathlib

theorem algebra_116220 (x : ℝ) : ⌊x⌋ * (x - ⌊x⌋) = x - 1 ↔ x ∈ Set.Ico 1 2 := by
  constructor
  · -- Assume ⌊x⌋ * (x - ⌊x⌋) = x - 1, prove x ∈ Set.Ico 1 2
    intro h
    have h1 : ⌊x⌋ ≤ (x : ℝ) := by
      exact Int.floor_le x
    have h2 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have eq1 : (⌊x⌋ : ℝ) * (x - (⌊x⌋ : ℝ)) = x - 1 := by
      simpa using h
    have h4 : ⌊x⌋ ≤ 1 := by
      by_contra h4
      push_neg at h4
      have h5 : ⌊x⌋ ≥ 2 := by omega
      have h8 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
        exact_mod_cast h5
      nlinarith [h1, h2, eq1, h8]
    have h5 : ⌊x⌋ ≥ 1 := by
      by_contra h5
      push_neg at h5
      have h6 : ⌊x⌋ ≤ 0 := by omega
      have h7 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by
        exact_mod_cast h6
      nlinarith [h1, h2, eq1, h7]
    have h7 : ⌊x⌋ = 1 := by omega
    have h8 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h7
    constructor
    · -- 1 ≤ x
      have h9 : 1 ≤ (x : ℝ) := by
        have h11 : (⌊x⌋ : ℝ) ≤ (x : ℝ) := by
          exact Int.floor_le x
        rw [h8] at h11
        linarith
      linarith
    · -- x < 2
      have h10 : (x : ℝ) < (2 : ℝ) := by
        have h12 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one x
        rw [h8] at h12
        linarith
      linarith
  · -- Assume x ∈ Set.Ico 1 2, prove ⌊x⌋ * (x - ⌊x⌋) = x - 1
    rintro ⟨h1, h2⟩
    have h3 : ⌊x⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try linarith)
    have h4 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h3
    rw [h4]
    have h7 : (1 : ℝ) * (x - (1 : ℝ)) = x - 1 := by
      linarith
    simpa using h7