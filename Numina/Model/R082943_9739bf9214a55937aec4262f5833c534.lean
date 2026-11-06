import Mathlib

theorem number_theory_6034 :
    ∑ᶠ x ∈ {x : ℤ | 0 < x ∧ ∃ n : ℤ, 0 < n ∧ x ^ 2 + 81 = n ^ 2}, x = 52 := by
  have h1 : {x : ℤ | 0 < x ∧ ∃ n : ℤ, 0 < n ∧ x ^ 2 + 81 = n ^ 2} = {12, 40} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, we show that if x is in the set, then x ∈ {12, 40}
      rintro ⟨hx_pos, ⟨n, hn_pos, heq⟩⟩
      have h1 : n ^ 2 - x ^ 2 = 81 := by nlinarith
      have h2 : (n - x) * (n + x) = 81 := by nlinarith
      have h3 : n - x > 0 := by nlinarith [sq_pos_of_pos hx_pos, sq_pos_of_pos hn_pos]
      have h4 : n > x := by nlinarith [sq_pos_of_pos hx_pos, sq_pos_of_pos hn_pos, h1]
      have h5 : n - x ∣ 81 := by
        use n + x
        nlinarith
      have h6 : n - x ≤ 81 := by
        exact Int.le_of_dvd (by norm_num) h5
      interval_cases h : n - x <;> omega
    · -- Now, we prove the reverse direction. If x ∈ {12, 40}, then x is in the set
      rintro (rfl | rfl)
      · constructor
        · norm_num
        · use 15
          all_goals norm_num
      · constructor
        · norm_num
        · use 41
          all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num
  <;> tauto