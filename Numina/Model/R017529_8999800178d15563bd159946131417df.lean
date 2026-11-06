import Mathlib

theorem algebra_5154 :
  ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ (n ^ 2 + 283 * n + 2022) % (n + 7) = 0}, n = 168 := by
  have h1 : {n : ℕ | 0 < n ∧ (n ^ 2 + 283 * n + 2022) % (n + 7) = 0} = {2, 3, 8, 11, 23, 38, 83} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume $n > 0$ and $(n^2 + 283n + 2022) \% (n + 7) = 0$,
      rintro ⟨hn_pos, h⟩
      have h2 : n + 7 ∣ n ^ 2 + 283 * n + 2022 := by
        have h3 : (n ^ 2 + 283 * n + 2022) % (n + 7) = 0 := h
        exact Nat.dvd_of_mod_eq_zero h3
      have h3 : n + 7 ∣ 90 := by
        have h4 : n + 7 ∣ n ^ 2 + 283 * n + 2022 := h2
        have h7 : n + 7 ∣ (n + 7) * (n + 276) := by
          simp [Nat.mul_assoc]
        have h8 : n + 7 ∣ (n ^ 2 + 283 * n + 2022 - (n + 7) * (n + 276)) := by
          apply Nat.dvd_sub'
          · exact h4
          · exact h7
        have h9 : (n ^ 2 + 283 * n + 2022) = (n + 7) * (n + 276) + 90 := by
          ring_nf
        have h10 : (n ^ 2 + 283 * n + 2022 - (n + 7) * (n + 276)) = 90 := by
          omega
        rw [h10] at h8
        exact h8
      have h4 : n ≤ 83 := by
        by_contra h
        push_neg at h
        have h6 : n + 7 > 90 := by omega
        have h7 : (n + 7) ∣ 90 := h3
        have h8 : (n + 7) ≤ 90 := by
          exact Nat.le_of_dvd (by norm_num) h7
        omega
      interval_cases n <;> norm_num at h2 h3 h ⊢
      <;> tauto
    · -- Show that $n \in \{2, 3, 8, 11, 23, 38, 83\}$,
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> rfl