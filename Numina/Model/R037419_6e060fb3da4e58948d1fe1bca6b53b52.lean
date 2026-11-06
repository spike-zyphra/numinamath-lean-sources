import Mathlib

theorem number_theory_216587 :
    {n : ℕ | 0 < n ∧ (∑ i ∈ Finset.range 10, (n + i)) ∣ (∑ i ∈ Finset.range 10, (n + i)^2)} = {1, 12} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First direction: prove that if n is in the set, then n ∈ {1, 12}
    intro h
    rcases h with ⟨hn_pos, hdiv⟩
    have h1 : (∑ i in Finset.range 10, (n + i)) = 10 * n + 45 := by
      simp [Finset.sum_range_succ]
      all_goals ring
    have h2 : (∑ i in Finset.range 10, (n + i)^2) = 10 * n^2 + 90 * n + 285 := by
      simp [Finset.sum_range_succ]
      all_goals ring
    rw [h1, h2] at hdiv
    have h3 : (10 * n + 45) ∣ (10 * n^2 + 90 * n + 285) := hdiv
    have h4 : (10 * n + 45) ∣ (45 * n + 285) := by
      have h5 : (10 * n + 45) ∣ (10 * n^2 + 90 * n + 285) := h3
      have h6 : (10 * n + 45) ∣ (n * (10 * n + 45)) := by
        use n
        all_goals ring
      have h7 : (10 * n + 45) ∣ ((10 * n^2 + 90 * n + 285) - (n * (10 * n + 45)) ) := by
        exact Nat.dvd_sub' h5 h6
      have h8 : ((10 * n^2 + 90 * n + 285) - (n * (10 * n + 45)) ) = (45 * n + 285) := by
        ring_nf
        <;> omega
      rw [h8] at h7
      exact h7
    have h9 : (10 * n + 45) ∣ 165 := by
      have h10 : (10 * n + 45) ∣ (2 * (45 * n + 285)) := by
        exact dvd_trans h4 (by simp)
      have h11 : (10 * n + 45) ∣ (9 * (10 * n + 45)) := by
        use 9
        all_goals ring
      have h12 : (10 * n + 45) ∣ (2 * (45 * n + 285) - (9 * (10 * n + 45)) ) := by
        apply Nat.dvd_sub'
        · exact h10
        · exact h11
      have h13 : (2 * (45 * n + 285) - (9 * (10 * n + 45)) ) = 165 := by
        ring_nf
        <;> omega
      rw [h13] at h12
      exact h12
    have h10 : (10 * n + 45) ≤ 165 := by
      exact Nat.le_of_dvd (by omega) h9
    have h11 : n ≤ 12 := by
      omega
    interval_cases n <;> norm_num at h9 h10 hdiv h11 ⊢
  · -- Backward direction: prove that if n ∈ {1, 12}, then n is in the set
    rintro (rfl | rfl)
    · -- First case: n = 1
      constructor
      · norm_num -- Check positivity
      · -- Check divisibility
        norm_num [Finset.sum_range_succ]
    · -- Second case: n = 12
      constructor
      · norm_num -- Check positivity
      · -- Check divisibility
        norm_num [Finset.sum_range_succ]