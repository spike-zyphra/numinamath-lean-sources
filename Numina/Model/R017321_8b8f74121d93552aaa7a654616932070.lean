import Mathlib

theorem algebra_302668 : {x : ℝ | 2006 * x + (x - ⌊x⌋) = 1 / 2007}.ncard = 2 := by 
  have h1 : {x : ℝ | 2006 * x + (x - ⌊x⌋) = 1 / 2007} = {1 / (2007 ^ 2 : ℝ), (-2006 / (2007 ^ 2 : ℝ))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume that x satisfies the equation
      intro h_eq
      have h2 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
      have h3 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
      have h_eq3 : (⌊x⌋ : ℝ) = 2007 * x - 1 / 2007 := by 
        linarith
      have h6 : ⌊x⌋ ≤ 0 := by
        by_contra h
        push_neg at h
        have h7 : ⌊x⌋ ≥ 1 := by linarith
        have h8 : (⌊x⌋ : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h7
        nlinarith [h3, h_eq3, h8]
      have h7 : ⌊x⌋ ≥ -1 := by
        by_contra h
        push_neg at h
        have h8 : ⌊x⌋ ≤ -2 := by linarith
        have h9 : (⌊x⌋ : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h8
        nlinarith [h2, h_eq3, h9]
      have h8 : ⌊x⌋ = 0 ∨ ⌊x⌋ = -1 := by omega
      rcases h8 with (h9 | h9)
      · -- case n = 0
        have h10 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h9
        have hx : x = (1 / (2007 ^ 2 : ℝ)) := by
          rw [h10] at h_eq3
          linarith
        left
        linarith
      · -- case n = -1
        have h11 : (⌊x⌋ : ℝ) = (-1 : ℝ) := by exact_mod_cast h9
        have hx : x = (-2006 / (2007 ^ 2 : ℝ)) := by
          rw [h11] at h_eq3
          linarith
        right
        linarith
    · -- Assume x is in the right side
      rintro (h_eq | h_eq)
      · -- Check the equation for x = 1/(2007^2)
        rw [h_eq]
        norm_num [Int.floor_eq_iff]
      · -- Check the equation for x = -2006/(2007^2)
        rw [h_eq]
        norm_num [Int.floor_eq_iff]
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]
  all_goals norm_num
  all_goals norm_num