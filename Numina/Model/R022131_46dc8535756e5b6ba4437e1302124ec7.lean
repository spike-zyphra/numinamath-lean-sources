import Mathlib

theorem number_theory_6377 :
    ∑ᶠ x ∈ {x : ℕ | 0 < x ∧ ∃ n : ℕ, 0 < n ∧ n^2 = x^2 + 91}, x = 48 := by
  have h1 : {x : ℕ | 0 < x ∧ ∃ n : ℕ, 0 < n ∧ n^2 = x^2 + 91} = {3, 45} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if x in the set {x : ℕ | 0 < x ∧ ∃ n : ℕ, 0 < n ∧ n^2 = x^2 + 91}, then x ∈ {3, 45}
      rintro ⟨hx, ⟨n, hn, h_eq⟩⟩
      have h2 : n > x := by
        by_contra h
        push_neg at h
        have h3 : n ≤ x := by linarith
        have h4 : n ^ 2 ≤ x ^ 2 := by nlinarith
        have h5 : x ^ 2 + 91 = n ^ 2 := by linarith [h_eq]
        nlinarith
      have h4 : n ≤ 50 := by
        nlinarith [sq_nonneg (n - x : ℤ), sq_nonneg (n - 46 : ℤ), sq_nonneg (x - 45 : ℤ), sq_nonneg (x - 3 : ℤ), h_eq, h2]
      have h5 : x ≤ 45 := by
        nlinarith [sq_nonneg (n - x : ℤ), sq_nonneg (n - 46 : ℤ), sq_nonneg (x - 45 : ℤ), sq_nonneg (x - 3 : ℤ), h_eq, h2]
      interval_cases x <;> try { 
        norm_num at h_eq
        all_goals 
        try { 
          have h6 : n ≤ 50 := by nlinarith 
          interval_cases n <;> omega 
        }
      }
    · -- Second direction: if x ∈ {3, 45}, then x in the set
      rintro (rfl | rfl)
      · -- Show 3 is in the set 
        constructor
        · norm_num
        · use 10
          all_goals norm_num
      · -- Show 45 is in the set 
        constructor
        · norm_num
        · use 46
          all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num