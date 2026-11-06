import Mathlib

theorem inequalities_325400 (a : ℝ) :
  {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0}.encard = 2 ↔ a ∈ Set.Ioo 0 1 := by
  constructor <;> intro h
  case mp =>
    rw [Set.encard_eq_two] at h
    obtain ⟨x₁, x₂, p, hx_set_eq_pair⟩ := h
    have hx₁_in_S : x₁ ∈ {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0} := by
      rw [hx_set_eq_pair]; simp
    have hx₂_in_S : x₂ ∈ {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0} := by
      rw [hx_set_eq_pair]; simp
    simp only [Set.mem_setOf_eq, sub_eq_zero] at hx₁_in_S hx₂_in_S
    obtain ⟨hx₁_pos, hx₁_abs_eq_a⟩ := hx₁_in_S
    obtain ⟨hx₂_pos, hx₂_abs_eq_a⟩ := hx₂_in_S
    cases' eq_or_ne (2 * x₁ - 1) (2 * x₂ - 1) with h_eq h_ne <;>
    cases' le_total 0 (2 * x₁ - 1) with h_le1 h_le1 <;>
    cases' le_total 0 (2 * x₂ - 1) with h_le2 h_le2 <;>
    simp_all [abs_of_nonneg, abs_of_nonpos, sub_eq_zero]
    have q : x₁  = x₂ := by
      rw [← h_eq] at hx₁_abs_eq_a
      linarith
    contradiction
    have q : x₁  = x₂ := by
      rw [← h_eq] at hx₁_abs_eq_a
      linarith
    contradiction
    have q : a < 1 := by
      linarith
    by_cases ha_zero : a = 0
    · simp [ha_zero, abs_eq_zero, sub_eq_zero] at hx₁_abs_eq_a hx₂_abs_eq_a
      have p1 : 2 * x₁ ≠ 2 * x₂ := by
        intro h₁ 
        apply p 
        apply mul_left_cancel₀ (two_ne_zero' ℝ) 
        exact h₁ 
      rw [hx₁_abs_eq_a, hx₂_abs_eq_a] at p1 
      contradiction
    have ha_pos : a > 0 := lt_of_le_of_ne h_le1 (Ne.symm ha_zero)
    exact And.intro ha_pos q
    have q : a < 1 := by
      linarith
    by_cases ha_zero : a = 0
    · simp [ha_zero, abs_eq_zero, sub_eq_zero] at hx₁_abs_eq_a hx₂_abs_eq_a
      have p1 : 2 * x₁ ≠ 2 * x₂ := by
        intro h₁ 
        apply p 
        apply mul_left_cancel₀ (two_ne_zero' ℝ) 
        exact h₁ 
      rw [← hx₁_abs_eq_a, hx₂_abs_eq_a] at p1 
      contradiction
    have ha_pos : a > 0 := lt_of_le_of_ne h_le2 (Ne.symm ha_zero)
    exact And.intro ha_pos q

    have q : x₁  = x₂ := by
      rw [← hx₂_abs_eq_a] at hx₁_abs_eq_a
      linarith
    contradiction

  case mpr =>
    rw [Set.encard_eq_two]
    simp only [Set.mem_Ioo] at h
    obtain ⟨ha_pos, ha_lt_2⟩ := h
    let s₁ := (1 + a) / 2
    let s₂ := (1 - a) / 2
    have h_s_distinct : (1 + a) / 2 ≠ (1 - a) / 2 := by
      intro heq_s
      linarith [ha_pos]
    use (1 + a) / 2, (1 - a) / 2
    constructor
    · exact h_s_distinct
    · simp_rw [sub_eq_zero]
      ext y 
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      have f_trans : 0 < a → 0 ≤ a := by
        intro h
        linarith
      have hy_abs_eq_a_iff : abs (2 * y - 1) = a ↔ (y = (1 + a) / 2 ∨ y = (1 - a) / 2) := by
        rw [abs_eq (f_trans ha_pos)]
        constructor <;> intro h_sol_abs
        · rcases h_sol_abs
          · left;  linarith 
          · right; linarith 
        · rcases h_sol_abs
          · left;  linarith 
          · right; linarith 
      rw [hy_abs_eq_a_iff]
      constructor
      · exact And.right
      · intro hy_is_s1_or_s2
        constructor
        · cases hy_is_s1_or_s2
          · subst y; linarith [ha_pos]
          · subst y;  linarith [ha_lt_2]
        · exact hy_is_s1_or_s2