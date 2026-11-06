import Mathlib

theorem number_theory_311625 :
    Set.ncard {n : ℕ | ∃ k, n = k^2 ∧ Odd (Nat.digits 10 n)[1]! ∧ n ≤ 35^2} = 7 := by
  have : {n : ℕ | ∃ k, n = k^2 ∧ Odd (Nat.digits 10 n)[1]! ∧ n ≤ 35^2} = {16, 36, 196, 256, 576, 676, 1156} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n in LHS.
      rintro ⟨k, rfl, hk1, hk2⟩
      have h1 : k ≤ 35 := by
        by_contra h2
        push_neg at h2
        have h3 : k ^ 2 > 35 ^ 2 := by
          nlinarith [h2]
        have h4 : k ^ 2 ≤ 35 ^ 2 := by linarith
        linarith
      interval_cases k <;> norm_num [Nat.odd_iff] at *
      <;> omega
    · -- Assume n in RHS.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 16
        refine ⟨4, by norm_num, ?_, by norm_num⟩
        native_decide
      · -- 36
        refine ⟨6, by norm_num, ?_, by norm_num⟩
        native_decide
      · -- 196
        refine ⟨14, by norm_num, ?_, by norm_num⟩
        native_decide
      · -- 256
        refine ⟨16, by norm_num, ?_, by norm_num⟩
        native_decide
      · -- 576
        refine ⟨24, by norm_num, ?_, by norm_num⟩
        native_decide
      · -- 676
        refine ⟨26, by norm_num, ?_, by norm_num⟩
        native_decide
      · -- 1156
        refine ⟨34, by norm_num, ?_, by norm_num⟩
        native_decide
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }