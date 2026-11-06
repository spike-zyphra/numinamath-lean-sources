import Mathlib

theorem inequalities_303151 (a : ℝ) (ha : a ≠ 0) :
    {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} = {1, 2, 3} ↔
    -1 ≤ a ∧ a < -3 / 4 := by
  constructor
  · -- Assume {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} = {1, 2, 3}, prove -1 ≤ a ∧ a < -3 / 4.
    intro h_eq
    have h1 : 1 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by
      rw [h_eq]
      simp
    have h12 : a * (1 : ℝ) + 3 ≥ 0 := by 
      have h1' : (1 : ℕ) ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := h1
      simp at h1'
      norm_num at h1' ⊢
      linarith
    have h2 : 2 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by 
      rw [h_eq]
      simp
    have h22 : a * (2 : ℝ) + 3 ≥ 0 := by 
      have h2' : (2 : ℕ) ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := h2
      simp at h2'
      norm_num at h2' ⊢
      linarith
    have h3 : 3 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by 
      rw [h_eq]
      simp
    have h32 : a * (3 : ℝ) + 3 ≥ 0 := by 
      have h3' : (3 : ℕ) ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := h3
      simp at h3'
      norm_num at h3' ⊢
      linarith
    have h4 : 4 ∉ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by 
      rw [h_eq]
      simp
    have h41 : ¬ (a * (4 : ℝ) + 3 ≥ 0) := by 
      by_contra h42
      have h4_in : 4 ∈ {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} := by 
        simp
        <;> norm_num at h42 ⊢
        all_goals linarith
      contradiction
    constructor
    · -- Show that -1 ≤ a
      nlinarith
    · -- Show that a < -3 / 4
      by_contra h43
      push_neg at h43
      have h43 : a * (4 : ℝ) + 3 ≥ 0 := by nlinarith
      have h41' : a * (4 : ℝ) + 3 ≥ 0 := h43
      have h41' : a * (4 : ℝ) + 3 ≥ 0 := h43
      exfalso
      apply h41
      linarith
  · -- Assume -1 ≤ a ∧ a < -3 / 4, prove {x : ℕ | x > 0 ∧ a * x + 3 ≥ 0} = {1, 2, 3}.
    rintro ⟨ha1, ha2⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x > 0 ∧ a * x + 3 ≥ 0, show x ∈ {1, 2, 3}
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h5 : x ≤ 3 := by
        by_contra h6
        push_neg at h6
        have h7 : x ≥ 4 := by omega
        have h8 : (x : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h7
        -- Show contradiction a * (4 : ℝ) + 3 < (0 : ℝ)
        have h9 : a * (x : ℝ) + 3 < (0 : ℝ) := by
          have h10 : a < (-3 / 4 : ℝ) := by linarith
          nlinarith [show (x : ℝ) ≥ (4 : ℝ) by exact_mod_cast h7, sq_nonneg (a + 1 : ℝ)]
        linarith
      interval_cases x <;> norm_num at hx1 hx2 ⊢ <;> tauto
    · -- Assume x ∈ {1, 2, 3}, show x > 0 ∧ a * x + 3 ≥ 0
      rintro (rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        · norm_num
          all_goals
          nlinarith
      · -- x = 2
        constructor
        · norm_num
        · norm_num
          all_goals
          nlinarith
      · -- x = 3
        constructor
        · norm_num
        · norm_num
          all_goals
          nlinarith