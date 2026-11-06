import Mathlib

theorem algebra_3928 :
  ∑ᶠ x ∈ {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ (1 / 8 + 1 / x : ℝ) = 1 / y}, x = 88 := by
  have h1 : {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ (1 / 8 + 1 / x : ℝ) = 1 / y} = {8, 24, 56} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in the set, prove x \in \{8, 24, 56\}
      intro h
      rcases h with ⟨y, hx_pos, hy_pos, heq⟩
      have eq1 : (x : ℝ) > (0 : ℝ) := by
        exact_mod_cast hx_pos
      have eq2 : (y : ℝ) > (0 : ℝ) := by
        exact_mod_cast hy_pos
      have h2 : (x : ℝ) * (y : ℝ) + 8 * (y : ℝ) = 8 * (x : ℝ) := by
        field_simp at heq ⊢
        nlinarith [heq]
      have h3 : x * y + 8 * y = 8 * x := by
        exact_mod_cast h2
      have h4 : x ≤ 64 := by
        by_contra h4
        push_neg at h4
        have eq5 : x * y + 8 * y = 8 * x := h3
        have eq6 : y ≤ 8 := by
          nlinarith [sq_nonneg ((x : ℕ) : ℕ), sq_nonneg ((y : ℕ) : ℕ)]
        interval_cases y <;> omega
      interval_cases x <;> omega
    · -- Show the reverse direction
      rintro (rfl | rfl | rfl)
      · -- x = 8
        use 4
        norm_num
      · -- x = 24
        use 6
        norm_num
      · -- x = 56
        use 7
        norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> try native_decide