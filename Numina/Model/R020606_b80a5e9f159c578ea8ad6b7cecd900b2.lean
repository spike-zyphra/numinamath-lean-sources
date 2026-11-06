import Mathlib

theorem number_theory_73324 : Set.ncard {n : ℤ | 0 ≤ n ∧ n < 840 ∧ n^8 - n^4 + n - 1 ≡ 0 [ZMOD 840]} = 2 := by 
  have h1 : {n : ℤ | 0 ≤ n ∧ n < 840 ∧ n^8 - n^4 + n - 1 ≡ 0 [ZMOD 840]} = {1, 241} := by 
    ext n 
    simp [Int.ModEq]
    constructor
    · -- Assume n is in the set, need to prove n = 1 or n = 241
      rintro ⟨h0, h1, h2⟩
      norm_num at h2
      have h3 : n ≤ 839 := by omega
      interval_cases n 
      all_goals omega
    · -- Assume n is in {1, 241}, need to prove it is in the set 
      rintro (rfl | rfl) 
      · constructor 
        · norm_num 
        constructor 
        · norm_num 
        · native_decide 
      · constructor 
        · norm_num 
        constructor 
        · norm_num 
        · native_decide 
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num