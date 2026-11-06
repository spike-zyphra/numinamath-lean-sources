import Mathlib

def a (n : ℕ) := 2 + (n - 1) * 1
def b (n : ℕ) := 1 * 2 ^ (n - 1)
def M (n : ℕ) := ∑ i in Finset.Icc 1 n, a (b i)

theorem algebra_302969 :
    Set.ncard {n | n ≥ 1 ∧ M n ≤ 2008} = 10 := by
  have h1 : {n | n ≥ 1 ∧ M n ≤ 2008} = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set, prove it's in {1, 2, ..., 10}
      intro h
      rcases h with ⟨h_n_ge_1, h_Mn_le_2008⟩
      have h2 : n ≤ 10 := by
        by_contra h3
        push_neg at h3
        have h3' : n ≥ 11 := by omega
        have h4 : M n > 2008 := by
          have h41 : ∀ n : ℕ, n ≥ 11 → M n > 2008 := by
            intro n hn
            have eq1 : M n ≥ M 11 := by
              have eq11 : M n = ∑ i in Finset.Icc 1 n, (a (b i)) := by
                simp [M]
              have eq12 : M 11 = ∑ i in Finset.Icc 1 11, (a (b i)) := by
                simp [M]
              rw [eq11, eq12]
              have eq13 : ∑ i in Finset.Icc 1 11, (a (b i)) ≤ ∑ i in Finset.Icc 1 n, (a (b i)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · -- Show Finset.Icc 1 11 ⊆ Finset.Icc 1 n when n ≥ 11
                  intro i hi
                  simp at hi ⊢
                  omega
                · -- Show that each term is ≤
                  intro i hi
                  simp [a, b] at hi ⊢
                  all_goals omega
              linarith
            have eq2 : M 11 > 2008 := by
              norm_num [M, a, b, Finset.sum_Icc_succ_top]
            have h5 : M n ≥ M 11 := eq1
            linarith [eq2, h5]
          specialize h41 n h3'
          simpa using h41
        linarith
      interval_cases n <;> norm_num [M, a, b, Finset.sum_Icc_succ_top] at h_Mn_le_2008 ⊢
      <;> tauto
    · -- Show the reverse direction
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
      · constructor
        · norm_num
        · norm_num [M, a, b, Finset.sum_Icc_succ_top]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]