import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_2144 (a : ℝ) :
  {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} = {1, 2, 3, 4} ↔
  -5 / 4 ≤ a ∧ a < -1 := by
  constructor
  · -- Assume {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} = {1, 2, 3, 4}, prove -5 / 4 ≤ a ∧ a < -1
    intro h
    have h1 : (1 : ℤ) ∈ {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} := by
      rw [h]
      simp
    rcases h1 with ⟨h1l, h1u⟩
    have h11 : a * (1 : ℝ) + 5 ≥ 0 := by
      norm_num at h1l
      nlinarith
    have h12 : a * (1 : ℝ) + 5 ≤ 4 := by
      norm_num at h1u
      nlinarith
    have h4 : (4 : ℤ) ∈ {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} := by
      rw [h]
      simp
    rcases h4 with ⟨h4l, h4u⟩
    have h41 : a * (4 : ℝ) + 5 ≥ 0 := by
      norm_num at h4l
      nlinarith
    have h42 : a * (4 : ℝ) + 5 ≤ 4 := by
      norm_num at h4u
      nlinarith
    have h5 : (5 : ℤ) ∉ {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} := by
      rw [h]
      simp
    -- More help for constraints
    have h61 : a ≥ -5 := by
      have h7 : a * (1 : ℝ) ≥ -5 := by nlinarith
      linarith
    have h62 : a ≤ -1 := by
      nlinarith
    have h63 : a ≥ -5 / 4 := by
      nlinarith
    have h64 : a < -1 := by
      by_contra h
      push_neg at h
      have ha1 : a = -1 := by
        nlinarith
      -- Now show contradiction
      have h8 : (5 : ℤ) ∈ {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} := by
        simp [ha1]
        all_goals norm_num
      -- This contradicts h5
      have h8' : (5 : ℤ) ∉ {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4} := h5
      contradiction
    constructor
    · -- deriv -5/4
      linarith
    · -- deriv a < -1
      linarith
  · -- Assume -5 / 4 ≤ a ∧ a < -1, prove the set equality
    rintro ⟨ha1, ha2⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4}, show x ∈ {1, 2, 3, 4}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≤ 4 := by
        by_contra h
        push_neg at h
        have hx5 : x ≥ 5 := by omega
        have h4 : (x : ℝ) ≥ (5 : ℝ) := by exact_mod_cast hx5
        nlinarith [show (0 : ℝ) ≤ (x : ℝ) from by nlinarith]
      have h4 : x ≥ 1 := by
        by_contra h
        push_neg at h
        have hx0 : x ≤ 0 := by omega
        have h5 : (x : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hx0
        nlinarith [show (x : ℝ) ≤ (0 : ℝ) from by nlinarith]
      interval_cases x <;> norm_num at h1 h2 ⊢
      <;> try { tauto }
      <;> norm_num at h1 h2 ⊢
      all_goals norm_num
    · -- Assume x ∈ {1, 2, 3, 4}, show x is in {x : ℤ | 0 ≤ a * x + 5 ∧ a * x + 5 ≤ 4}
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · -- Show 0 ≤a * (1 : ℝ) + 5
          norm_num
          all_goals nlinarith
        · -- Show a * (1 : ℝ) + 5 ≤4
          norm_num
          all_goals nlinarith
      · -- x = 2
        constructor
        · -- Show 0 ≤a * (2 : ℝ) + 5
          norm_num
          all_goals nlinarith
        · -- Show a * (2 : ℝ) + 5 ≤4
          norm_num
          all_goals nlinarith
      · -- x = 3
        constructor
        · -- Show 0 ≤a * (3 : ℝ) + 5
          norm_num
          all_goals nlinarith
        · -- Show a * (3 : ℝ) + 5 ≤4
          norm_num
          all_goals nlinarith
      · -- x = 4
        constructor
        · -- Show 0 ≤a * (4 : ℝ) + 5
          norm_num
          all_goals nlinarith
        · -- Show a * (4 : ℝ) + 5 ≤4
          norm_num
          all_goals nlinarith