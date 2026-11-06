import Mathlib

theorem number_theory_159142 :
    Set.ncard {x : ℤ | ⌊(-77.66 * x : ℝ)⌋ = ⌊(-77.66 : ℝ)⌋ * x + 1} = 3 := by

  have h1 : {x : ℤ | ⌊(-77.66 * x : ℝ)⌋ = ⌊(-77.66 : ℝ)⌋ * x + 1} = {3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]

    constructor
    · -- Assume x satisfies the equation
      intro h
      have h2 : ⌊(-77.66 : ℝ)⌋ = -78 := by
        norm_num [Int.floor_eq_iff]

      rw [h2] at h

      have eq1 : ⌊(-77.66 * (x : ℝ))⌋ = -78 * x + 1 := by
        simpa using h

      have h4 : ( -78 * (x : ℝ) + 1 ) ≤ ( -77.66 * (x : ℝ) ) := by
        have h5 : (⌊(-77.66 * (x : ℝ))⌋ : ℝ) ≤ (-77.66 * (x : ℝ)) := by
          exact Int.floor_le (-77.66 * (x : ℝ))
        have h6 : (⌊(-77.66 * (x : ℝ))⌋ : ℝ) = ( -78 * (x : ℝ) + 1 ) := by
          exact_mod_cast eq1
        nlinarith [h5, h6]

      have h7 : ( -77.66 * (x : ℝ) ) < ( -78 * (x : ℝ) + 2 ) := by
        have h8 : (-77.66 * (x : ℝ)) < (⌊(-77.66 * (x : ℝ))⌋ : ℝ) + 1 := by
          exact Int.lt_floor_add_one (-77.66 * (x : ℝ))
        have h9 : (⌊(-77.66 * (x : ℝ))⌋ : ℝ) = ( -78 * (x : ℝ) + 1 ) := by
          exact_mod_cast eq1
        nlinarith [h8, h9]

      have h8 : x ≥ 3 := by
        by_contra h9
        push_neg at h9
        have h9 : x ≤ 2 := by omega
        have h9' : x ≤ 2 := by omega
        have h12 : (x : ℝ) ≤ (2 : ℝ) := by exact_mod_cast h9'
        nlinarith

      have h9 : x ≤ 5 := by
        by_contra h9
        push_neg at h9
        have h9 : x ≥ 6 := by omega
        have h9' : x ≥ 6 := by omega
        have h12 : (x : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h9'
        nlinarith

      interval_cases x <;> tauto

    · -- Now prove the reverse implication
      rintro (rfl | rfl | rfl)
      · -- x = 3
        norm_num [Int.floor_eq_iff]
      · -- x = 4
        norm_num [Int.floor_eq_iff]
      · -- x = 5
        norm_num [Int.floor_eq_iff]

  rw [h1]
  norm_num