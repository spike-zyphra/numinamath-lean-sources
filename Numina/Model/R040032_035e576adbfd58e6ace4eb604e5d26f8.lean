import Mathlib

theorem number_theory_13804 (s : Set ℕ) (hs : s = {N : ℕ | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    a * b * c = 6 * (a + b + c) ∧ a = b + c ∧ N = a * b * c}) :
    ∑ᶠ N ∈ s, N = 336 := by 
  have h1 : s = {84, 96, 156} := by
    ext N
    simp only [hs, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h : N ∈ s
      rintro ⟨a, b, c, ha, hb, hc, h_eq1, h_eq2, h_eq3⟩
      rw [h_eq3] at *
      rw [show a = b + c by linarith [h_eq2]] at h_eq1
      have h2 : b * c = 12 := by
        nlinarith
      have h3 : b ≤ 12 := by
        by_contra h
        push_neg at h
        have h4 : c = 0 := by
          nlinarith
        all_goals
          nlinarith
      have h5 : c ≤ 12 := by
        by_contra h
        push_neg at h
        have h6 : b = 0 := by
          nlinarith
        all_goals
          nlinarith
      interval_cases b <;> try { 
        omega
      }
      all_goals
        try { 
          interval_cases c <;> omega 
        }
    · -- Assume h : N ∈ {84, 96, 156}
      rintro (rfl | rfl | rfl)
      · -- Let N = 84, which is from a = 7, b = 3, c = 4.
        refine' ⟨7, 3, 4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Let N = 96, which is from a = 8, b = 2, c = 6.
        refine' ⟨8, 2, 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Let N = 156, which is from a = 13, b = 1, c = 12.
        refine' ⟨13, 1, 12, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> try { native_decide }
  all_goals
    try { native_decide }
    <;> try { native_decide }