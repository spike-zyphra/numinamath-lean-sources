import Mathlib

theorem algebra_5463 :
    ∑ᶠ a ∈ {x : ℕ | ∃ b : ℕ, 0 < x ∧ 0 < b ∧ x < b ∧ (1 / x : ℚ) + (1 / b : ℚ) = 2 / 9}, a = 11 := by
  have h1 : {x : ℕ | ∃ b : ℕ, 0 < x ∧ 0 < b ∧ x < b ∧ (1 / x : ℚ) + (1 / b : ℚ) = 2 / 9} = {5, 6} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume that there exists b such that $0 < a ∧ 0 < b ∧ a < b ∧ (1 / a : ℚ) + (1 / b : ℚ) = 2 / 9$
      rintro ⟨b, ha_pos, hb_pos, h1, heq⟩
      have h2 : (a: ℚ) > 0 := by exact_mod_cast (show (a : ℕ) > 0 by linarith)
      have h3 : (b: ℚ) > 0 := by exact_mod_cast (show (b : ℕ) > 0 by linarith)
      have heq1 : (9: ℚ) * (b) + (9 : ℚ) * (a) = 2 * (a) * (b) := by
        have h5 : ( (1 / (a: ℚ)) + (1 / (b: ℚ)) ) = (2 / (9: ℚ)) := by linarith [heq]
        field_simp [show (a : ℚ) ≠ 0 by positivity, show (b : ℚ) ≠ 0 by positivity] at h5 ⊢
        nlinarith
      have h5 : (9: ℤ) * (b: ℤ) + (9: ℤ) * (a: ℤ) = 2 * (a: ℤ) * (b: ℤ) := by
        exact_mod_cast heq1
      have h6 : a ≤ 45 := by
        have h7 : a < b := h1
        by_contra h
        push_neg at h
        have h7 : a ≥ 46 := by omega
        have h8 : b ≥ 47 := by omega
        nlinarith
      have h7 : a = 5 ∨ a = 6 := by
        have h8 : a ≤ 45 := h6
        interval_cases a <;> omega
      cases h7 with
      | inl h8 => 
        omega
      | inr h8 => 
        omega
    · -- Show $a = 5, 6$ satisfies existence of $b$.
      rintro (h_eq | h_eq)
      · -- a = 5
        rw [h_eq]
        use 45
        all_goals norm_num
      · -- a = 6
        rw [h_eq]
        use 18
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num