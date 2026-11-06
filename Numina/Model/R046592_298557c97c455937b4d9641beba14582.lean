import Mathlib

theorem algebra_20743 : {x : ℝ | 0 < x ∧ x * ⌊x⌋ = 27} = {5.4} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x in the set, so 0 < x and x * floor x = 27, prove x = 5.4
    rintro ⟨hx1, hx2⟩

    have h1 : ⌊x⌋ ≤ (x : ℝ) := by 
      exact Int.floor_le x

    have h2 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by 
      exact Int.lt_floor_add_one x

    have h3 : (⌊x⌋ : ℝ) ≤ x := by 
      exact_mod_cast h1

    have h4 : x < (⌊x⌋ + 1 : ℝ) := by 
      exact_mod_cast h2

    have h5 : ⌊x⌋ ≤ 5 := by 
      by_contra h
      push_neg at h 
      have h6 : ⌊x⌋ ≥ 6 := by 
        omega
      have h7 : (⌊x⌋ : ℝ) ≥ (6 : ℝ) := by 
        exact_mod_cast h6 
      nlinarith

    have h6 : ⌊x⌋ ≥ 5 := by 
      by_contra h 
      push_neg at h 
      have h7 : ⌊x⌋ ≤ 4 := by 
        omega 
      have h8 : (⌊x⌋ : ℝ) ≤ (4 : ℝ) := by 
        exact_mod_cast h7 
      nlinarith

    have h7 : ⌊x⌋ = 5 := by 
      linarith 
    have h8 : (⌊x⌋ : ℝ) = (5 : ℝ) := by 
      exact_mod_cast h7 
    have h9 : x * (5 : ℝ) = 27 := by 
      rw [show (⌊x⌋ : ℝ) = (5 : ℝ) by exact_mod_cast h7] at hx2 
      linarith 
    have h10 : x = (27 / (5 : ℝ)) := by 
      linarith 
    rw [h10]
    norm_num 
  · -- Assume x = 5.4, prove 0 < x ∧ x * ⌊x⌋ = 27
    intro h
    rw [h] at *
    constructor
    · -- Show x > 0 
      norm_num 
    · -- Show x * floor x = 27 
      norm_num [Int.floor_eq_iff]