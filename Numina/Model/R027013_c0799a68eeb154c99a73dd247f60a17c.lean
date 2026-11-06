import Mathlib

theorem number_theory_5454 : {n : ℕ | 0 < n ∧ (n ^ 2 + 2019) % (n + 1) = 0}.encard = 11 := by
  have h1 : {n : ℕ | 0 < n ∧ (n ^ 2 + 2019) % (n + 1) = 0} = {1, 3, 4, 9, 19, 201, 403, 504, 100, 1009, 2019} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if $n$ is a solution, then $n \in \{1, 3, 4, 9, 19, 201, 403, 504, 100, 1009, 2019\}$.
      rintro ⟨hn_pos, h⟩
      have h2 : (n ^ 2 + 2019) % (n + 1) = 0 := h
      have h3 : n + 1 ∣ 2020 := by
        have h4 : n + 1 ∣ n ^ 2 + 2019 := by
          exact Nat.dvd_of_mod_eq_zero h2
        have h5 : n + 1 ∣ 2020 := by
          have h7 : n + 1 ∣ n ^ 2 + 2019 := h4
          have h8 : n + 1 ∣ (n + 1) * (n - 1) := by
            simp [Nat.mul_comm]
          have h9 : n + 1 ∣ (n ^ 2 + 2019) - (n + 1) * (n - 1) := by
            apply Nat.dvd_sub'
            · exact h7
            · exact h8
          have h10 : (n ^ 2 + 2019) - (n + 1) * (n - 1) = 2020 := by
            cases n with
            | zero => omega
            | succ n =>
              simp [Nat.mul_add, Nat.add_mul, mul_add, mul_assoc]
              <;> ring_nf
              <;> omega
          rw [h10] at h9
          exact h9
        exact h5
      have h4 : n ≤ 2019 := by
        by_contra h5
        push_neg at h5
        have h8 : n + 1 > 2020 := by omega
        have h9 : n + 1 ∣ 2020 := h3
        have h10 : n + 1 ≤ 2020 := by
          exact Nat.le_of_dvd (by omega) h9
        linarith
      interval_cases n <;> norm_num at h3 h2 ⊢ <;> tauto
    · -- Second direction: if $n \in \{1, 3, 4, 9, 19, 201, 403, 504, 100, 1009, 2019\}$, then $n$ is a solution.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        constructor
        · norm_num
        · norm_num
      · -- n = 3
        constructor
        · norm_num
        · norm_num
      · -- n = 4
        constructor
        · norm_num
        · norm_num
      · -- n = 9
        constructor
        · norm_num
        · norm_num
      · -- n = 19
        constructor
        · norm_num
        · norm_num
      · -- n = 201
        constructor
        · norm_num
        · norm_num
      · -- n = 403
        constructor
        · norm_num
        · norm_num
      · -- n = 504
        constructor
        · norm_num
        · norm_num
      · -- n = 100
        constructor
        · norm_num
        · norm_num
      · -- n = 1009
        constructor
        · norm_num
        · norm_num
      · -- n = 2019
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }