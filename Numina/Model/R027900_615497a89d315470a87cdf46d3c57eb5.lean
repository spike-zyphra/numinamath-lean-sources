import Mathlib

theorem number_theory_4771 :
  Set.encard {n : ℤ | (n - 2) ∣ (n ^ 3 : ℤ)} = 8 := by
  have h1 : {n : ℤ | (n - 2) ∣ (n ^ 3 : ℤ)} = {-6, -2, 0, 1, 3, 4, 6, 10} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if $(n - 2) \mid n^3$, then $n \in \{-6, -2, 0, 1, 3, 4, 6, 10\}$
      intro h
      have h2 : (n - 2) ∣ n^3 := h
      have h3 : (n - 2) ∣ 8 := by
        have h4 : (n - 2) ∣ n^3 := h2
        have h5 : (n - 2) ∣ (n - 2) * (n^2 + 2 * n + 4) := by 
          use n^2 + 2 * n + 4
          all_goals ring
        have h7 : (n - 2) ∣ (n ^ 3 - (n - 2) * (n^2 + 2 * n + 4)) := by
          apply Dvd.dvd.sub
          · exact h4
          · exact h5
        have h8 : (n ^ 3 - (n - 2) * (n^2 + 2 * n + 4)) = 8 := by
          nlinarith [sq_nonneg (n + 2), sq_nonneg (n - 2)]
        rw [h8] at h7
        exact h7
      have h4 : n - 2 ∣ 8 := h3
      have h5 : n - 2 ≤ 8 := by
        apply Int.le_of_dvd (by norm_num) h4
      have h6 : n - 2 ≥ -8 := by 
        have h7 : -(n - 2) ∣ 8 := by
          exact Int.neg_dvd.2 h4
        have h8 : -(n - 2) ≤ 8 := by 
          apply Int.le_of_dvd (by norm_num) h7
        omega
      have h7 : n - 2 = -8 ∨ n - 2 = -4 ∨ n - 2 = -2 ∨ n - 2 = -1 ∨
               n - 2 = 1 ∨ n - 2 = 2 ∨ n - 2 = 4 ∨ n - 2 = 8 := by
        interval_cases h : n - 2 <;> tauto
      rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7)
      · -- n - 2 = -8, so n = -6
        omega
      · -- n - 2 = -4, so n = -2
        omega
      · -- n - 2 = -2, so n = 0
        omega
      · -- n - 2 = -1, so n = 1
        omega
      · -- n - 2 = 1, so n = 3
        omega
      · -- n - 2 = 2, so n = 4
        omega
      · -- n - 2 = 4, so n = 6
        omega
      · -- n - 2 = 8, so n = 10
        omega
    · -- Second direction: each integer in the set satisfies the divisibility
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp
  <;> aesop