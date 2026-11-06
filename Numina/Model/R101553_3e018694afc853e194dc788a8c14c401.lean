import Mathlib

theorem algebra_20385 :
    Set.ncard {m : ℕ | 1 ≤ m ∧ m ≤ 1000 ∧ ∃ n : ℕ, 0 < n ∧ m * n ≤ m + n} = 1000 := by
  have h1 : {m : ℕ | 1 ≤ m ∧ m ≤ 1000 ∧ ∃ n : ℕ, 0 < n ∧ m * n ≤ m + n} = Set.Icc 1 1000 := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Prove the forward direction: that the set is contained in [1, 1000]
      intro h
      rcases h with ⟨hm1, hm2, ⟨n, ⟨hn1, hmn⟩⟩⟩
      exact ⟨hm1, hm2⟩
    · -- Prove the reverse direction: that any m in [1, 1000] is in the set
      rintro ⟨hm1, hm2⟩
      exact ⟨hm1, hm2, ⟨1, by norm_num, by
        nlinarith
      ⟩⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.Icc]
  <;> try { native_decide }