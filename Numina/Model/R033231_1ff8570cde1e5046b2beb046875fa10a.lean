import Mathlib

theorem number_theory_192885 (a : ℕ) (ha : a ≤ 72) (h : (a / 72 : ℚ) = {p | p.Prime ∧ p ∈ Finset.Icc 1 6}.ncard / 6) :
    a = 36 := by
  have h1 : {p | p.Prime ∧ p ∈ Finset.Icc 1 6} = {2, 3, 5} := by
    ext p
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume p is prime and in [1, 6]
      intro h
      rcases h with ⟨h_prime, ⟨h1, h6⟩⟩
      interval_cases p <;> norm_num at h_prime h1 h6 ⊢ <;> tauto
    · -- Assume p ∈ {2, 3, 5}
      rintro (rfl | rfl | rfl)
      · -- p = 2
        constructor
        · norm_num
        all_goals norm_num
      · -- p = 3
        constructor
        · norm_num
        all_goals norm_num
      · -- p = 5
        constructor
        · norm_num
        all_goals norm_num
  have h2 : {p | p.Prime ∧ p ∈ Finset.Icc 1 6}.ncard = 3 := by
    rw [h1]
    norm_num
  rw [h2] at h
  have h3 : (a : ℚ) = 36 := by
    field_simp at h ⊢
    linarith
  have h4 : a = 36 := by
    exact_mod_cast h3
  exact h4