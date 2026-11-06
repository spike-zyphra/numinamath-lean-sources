import Mathlib

theorem number_theory_5483 :
    Set.ncard {n : ℕ | 0 < n ∧ (n + 1) ∣ (n ^ 2 + 2019)} = 11 := by
  have h1 : {n : ℕ | 0 < n ∧ (n + 1) ∣ (n ^ 2 + 2019)} = {1, 3, 4, 9, 19, 100, 201, 403, 504, 1009, 2019} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n > 0 and n + 1 divides n^2 + 2019.
      rintro ⟨hn_pos, hdiv⟩
      have h3 : n + 1 ∣ 2020 := by
        have h4 : n + 1 ∣ n ^ 2 + 2019 := hdiv
        have h6 : (n + 1 : ℤ) ∣ (n ^ 2 + 2019 : ℤ) := by
          exact_mod_cast h4
        have h7 : (n + 1 : ℤ) ∣ (n ^ 2 + 2019 : ℤ) - (n + 1) * ((n - 1 : ℤ)) := by
          apply Dvd.dvd.sub
          · exact h6
          · apply dvd_mul_right
        have h8 : (n ^ 2 + 2019 : ℤ) - (n + 1) * ((n - 1 : ℤ)) = 2020 := by
          cases n with
          | zero =>
            omega -- contradicts with n > 0
          | succ n =>
            simp [mul_add, sub_mul, add_mul, mul_sub, pow_two]
            <;> ring
        have h9 : (n + 1 : ℤ) ∣ (2020 : ℤ) := by
          rw [h8] at h7
          exact_mod_cast h7
        have h10 : (n + 1) ∣ 2020 := by
          exact_mod_cast h9
        exact_mod_cast h10
      have h5 : n ≤ 2019 := by
        by_contra h
        push_neg at h
        have h6 : n + 1 > 2020 := by
          omega
        have h7 : (n + 1) ∣ 2020 := h3
        have h8 : n + 1 ≤ 2020 := by
          exact Nat.le_of_dvd (by norm_num) h7
        omega
      interval_cases n <;> norm_num at hdiv ⊢ <;> tauto
    · -- Show that if n in the right side, it's in the left side.
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
      · -- n = 100
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
      · -- n = 1009
        constructor
        · norm_num
        · norm_num
      · -- n = 2019
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp