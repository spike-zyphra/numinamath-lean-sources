import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_7962 (a : ℝ) :
  {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} = {1, 2, 3, 4} ↔
  -3 / 4 ≤ a ∧ a < -3 / 5 := by
  constructor
  · -- Assume {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} = {1, 2, 3, 4}, prove -3/4 ≤ a ∧ a < -3/5
    intro h
    have h1 : 1 ∈ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h2 : 2 ∈ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h3 : 3 ∈ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h4 : 4 ∈ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h5 : 5 ∉ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
      all_goals try { norm_num }
    simp at h1 h2 h3 h4 h5
    norm_num at h1 h2 h3 h4 h5
    constructor
    · -- Prove -3/4 ≤ a
      norm_num at h1 h2 h3 h4 h5
      linarith
    · -- Prove a < -3/5
      norm_num at h1 h2 h3 h4 h5
      linarith
  · -- Assume -3/4 ≤ a ∧ a < -3/5, prove {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0} = {1, 2, 3, 4}
    rintro ⟨h1, h2⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x ∈ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0}, prove x ∈ {1, 2, 3, 4}
      intro h
      rcases h with ⟨hx1, h1⟩
      have hx2 : x > 0 := by linarith
      have h2 : a * (x : ℝ) + 3 ≥ 0 := by
        exact_mod_cast h1
      by_cases h3 : x ≤ 4
      · -- If x ≤ 4, then x is in {1, 2, 3, 4}
        interval_cases x <;> simp <;> try tauto
      · -- If x > 4, then x ≥ 5
        push_neg at h3
        have hx4 : x ≥ 5 := by omega
        have h3' : (x : ℝ) ≥ (5 : ℝ) := by exact_mod_cast hx4
        nlinarith
    · -- Assume x ∈ {1, 2, 3, 4}, prove x ∈ {x : ℤ | 0 < x ∧ a * x + 3 ≥ 0}
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        · norm_num
          nlinarith
      · -- x = 2
        constructor
        · norm_num
        · norm_num
          nlinarith
      · -- x = 3
        constructor
        · norm_num
        · norm_num
          nlinarith
      · -- x = 4
        constructor
        · norm_num
        · norm_num
          nlinarith