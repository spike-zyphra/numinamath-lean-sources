import Mathlib

theorem number_theory_295154 :
    Set.ncard {n : ℕ | 2015 < n ∧ (n - 2015) ∣ n} = 8 := by
  have h1 : {n : ℕ | 2015 < n ∧ (n - 2015) ∣ n} = {2016, 2020, 2028, 2046, 2080, 2170, 2418, 4030} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n > 2015 and (n - 2015) divides n.
      intro h
      rcases h with ⟨h_gt, hdiv⟩
      have h3 : n - 2015 ∣ n := hdiv
      have h3' : n - 2015 ∣ 2015 := by
        have h5 : n - 2015 ∣ n := hdiv
        have h6 : n - 2015 ∣ n - 2015 := by
          apply Nat.dvd_refl
        have h7 : n - 2015 ∣ (n - (n - 2015)) := Nat.dvd_sub' h5 h6
        have h8 : n - (n - 2015) = 2015 := by
          omega
        rw [h8] at h7
        exact h7
      have h4 : n - 2015 ≤ 2015 := by
        apply Nat.le_of_dvd
        · norm_num
        · exact h3'
      have h0 : n - 2015 ≤ 2015 := h4
      have h7 : n ≤ 4030 := by
        omega
      interval_cases n <;> norm_num at h3 h3' ⊢ <;> tauto
    · -- Show that each element in the singleton set is in the original set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show 2016 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 2020 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 2028 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 2046 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 2080 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 2170 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 2418 in the original set
        constructor
        · norm_num
        all_goals norm_num
      · -- Show 4030 in the original set
        constructor
        · norm_num
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> native_decide