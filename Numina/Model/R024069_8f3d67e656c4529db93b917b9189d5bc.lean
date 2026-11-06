import Mathlib

theorem number_theory_95699 :
    Set.ncard {n : ℕ | n > 0 ∧ ∑ i in Finset.Icc 1 n, i ∣ 6 * n} = 5 := by

  have h1 : {n : ℕ | n > 0 ∧ ∑ i in Finset.Icc 1 n, i ∣ 6 * n} = {1, 2, 3, 5, 11} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n > 0 ∧ ∑ i in Finset.Icc 1 n, i ∣ 6 * n
      intro h
      rcases h with ⟨hn_pos, hdiv⟩
      have h2 : n ≥ 1 := by linarith
      have h3 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := by
        intro n
        induction n with
        | zero =>
          simp [Finset.sum_eq_zero]
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih]
          ring_nf
          <;> omega
      have h4 : ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := h3 n
      rw [h4] at hdiv
      have h5 : n * (n + 1) / 2 ∣ 6 * n := hdiv
      have h6 : n ≤ 11 := by
        by_contra h
        push_neg at h
        have h7 : n * (n + 1) / 2 ∣ 6 * n := hdiv
        have h8 : n * (n + 1) / 2 ≤ 6 * n := by
          exact Nat.le_of_dvd (by linarith) h7
        have h9 : n * (n + 1) ≥ 12 * n + 12 := by
          nlinarith [show n ≥ 12 by omega]
        have h10 : n * (n + 1) / 2 > 6 * n := by
          omega
        linarith
      interval_cases n <;> norm_num [Finset.sum_Icc_succ_top] at hdiv ⊢
      <;> tauto
    · -- Show that n ∈ {1, 2, 3, 5, 11} then n > 0 ∧ ∑ i in Finset.Icc 1 n, i ∣ 6 * n
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        constructor
        · norm_num
        · -- Show that the sum divides 6 * 1
          norm_num [Finset.sum_Icc_succ_top]
      · -- n = 2
        constructor
        · norm_num
        · -- Show that the sum divides 6 * 2
          norm_num [Finset.sum_Icc_succ_top]
      · -- n = 3
        constructor
        · norm_num
        · -- Show that the sum divides 6 * 3
          norm_num [Finset.sum_Icc_succ_top]
      · -- n = 5
        constructor
        · norm_num
        · -- Show that the sum divides 6 * 5
          norm_num [Finset.sum_Icc_succ_top]
      · -- n = 11
        constructor
        · norm_num
        · -- Show that the sum divides 6 * 11
          norm_num [Finset.sum_Icc_succ_top]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }