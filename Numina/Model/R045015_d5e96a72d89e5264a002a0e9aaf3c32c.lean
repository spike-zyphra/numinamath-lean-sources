import Mathlib

theorem algebra_13690 : {x : ℝ | ⌊x * ⌊x⌋⌋ = 29} = Set.Ico 5.8 6 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- Assume ⌊x * ⌊x⌋⌋ = 29, prove 5.8 ≤ x ∧ x < 6
    intro h
    have h1 : ⌊x * ⌊x⌋⌋ = 29 := h
    have h2 : 29 ≤ (x * ⌊x⌋ : ℝ) := by
      have h3 : (⌊x * ⌊x⌋⌋ : ℝ) ≤ x * ⌊x⌋ := by
        exact Int.floor_le (x * ⌊x⌋)
      have h4 : (⌊x * ⌊x⌋⌋ : ℝ) = (29 : ℝ) := by
        exact_mod_cast h1
      nlinarith
    have h3 : (x * ⌊x⌋ : ℝ) < (30 : ℝ) := by
      have h4 : x * ⌊x⌋ < (⌊x * ⌊x⌋⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (x * ⌊x⌋)
      have h5 : (⌊x * ⌊x⌋⌋ : ℝ) = (29 : ℝ) := by
        exact_mod_cast h1
      nlinarith
    have h4 : ⌊x⌋ ≤ (x : ℝ) := by
      exact Int.floor_le x
    have h5 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h6 : ⌊x⌋ ≤ 5 := by
      by_contra h7
      push_neg at h7
      have h7 : ⌊x⌋ ≥ 6 := by omega
      have h8 : (⌊x⌋ : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h7
      have h9 : x ≥ (6 : ℝ) := by
        nlinarith [h4, h8]
      have h10 : x * ⌊x⌋ ≥ (36 : ℝ) := by
        have h7 : (⌊x⌋ : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h7
        nlinarith [h4, h7, show (x) ≥ (6 : ℝ) by linarith]
      nlinarith
    have h7 : ⌊x⌋ ≥ -6 := by
      by_contra h8
      push_neg at h8
      have h8 : ⌊x⌋ ≤ -7 := by omega
      have h9 : (⌊x⌋ : ℝ) ≤ (-7 : ℝ) := by exact_mod_cast h8
      have h10 : x < (-6 : ℝ) := by
        have h11 : x < (⌊x⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one x
        have h12 : (⌊x⌋ : ℝ) ≤ (-7 : ℝ) := by
          exact_mod_cast h8
        nlinarith
      have h11 : x * ⌊x⌋ ≤ (x * (-7 : ℝ)) := by
        have h7 : (⌊x⌋ : ℝ) ≤ (-7 : ℝ) := by exact_mod_cast h8
        nlinarith [show (x) < 0 by nlinarith]
      have h12 : x * (-7 : ℝ) > (42 : ℝ) := by
        nlinarith
      have h13 : x * ⌊x⌋ < (30 : ℝ) := h3
      nlinarith
    interval_cases h90 : ⌊x⌋ <;> norm_num at h1 h2 h3 h4 h5 <;> norm_num [h90] at *
    all_goals
      try { 
        constructor <;> try linarith 
      } 
  · -- Assume 5.8 ≤ x ∧ x < 6, prove ⌊x * ⌊x⌋⌋ = 29
    rintro ⟨h1, h2⟩
    have h3 : ⌊x⌋ = 5 := by
      have h4 : 5 ≤ (x : ℝ) := by
        norm_num at h1 ⊢
        linarith
      have h5 : (x : ℝ) < (6 : ℝ) := by
        linarith
      have h6 : ⌊x⌋ = 5 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> try linarith
      exact h6
    have h7 : ⌊x * ⌊x⌋⌋ = 29 := by
      rw [h3]
      have h8 : 29 ≤ (x * (5 : ℝ) : ℝ) := by
        nlinarith
      have h9 : (x * (5 : ℝ) : ℝ) < (30 : ℝ) := by
        nlinarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith
    exact h7