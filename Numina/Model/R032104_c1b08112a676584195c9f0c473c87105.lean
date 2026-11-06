import Mathlib

theorem inequalities_314508 (a : ℝ) :
    {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} = {1, 2, 3} ↔
    a ∈ Set.Ico (-1) (-3 / 4) := by
  constructor
  · -- Assume {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} = {1, 2, 3}, prove a ∈ Set.Ico (-1) (-3 / 4)
    intro h
    have h1 : 1 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h2 : 2 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h3 : 3 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    have h4 : 4 ∉ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by
      rw [h]
      simp
    rcases h1 with ⟨ha1_pos, h1_ineq⟩
    rcases h2 with ⟨ha2_pos, h2_ineq⟩
    rcases h3 with ⟨ha3_pos, h3_ineq⟩
    norm_num at h1_ineq
    norm_num at h2_ineq
    norm_num at h3_ineq
    have h4_not_in_set : 4 ∉ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := h4
    simp at h4_not_in_set
    constructor
    · -- Show that -1 ≤ a
      linarith
    · -- Show that a < -3/4
      norm_num at h4_not_in_set ⊢
      linarith
  · -- Assume a ∈ Set.Ico (-1) (-3 / 4), prove {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} = {1, 2, 3}
    rintro ⟨ha1, ha2⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is a positive natural solution to the inequality
      rintro ⟨hx1, hx2⟩
      have h1 : (x : ℝ) > (0 : ℝ) := by
        exact_mod_cast hx1
      by_cases h2 : x ≤ 3
      · interval_cases x <;> norm_num at hx1 hx2 ⊢ <;> tauto
      · -- Assume x > 3
        push_neg at h2
        have h3 : x ≥ 4 := by omega
        have hx4 : (x : ℝ) ≥ (4 : ℝ) := by
          exact_mod_cast h3
        norm_num at hx2
        nlinarith
    · -- Show that if x ∈ {1, 2, 3}, then x is a positive natural solution
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
          linarith
      · constructor
        · norm_num
        · norm_num
          linarith
      · constructor
        · norm_num
        · norm_num
          linarith