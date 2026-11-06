import Mathlib

theorem number_theory_278234 :
    Set.ncard {n : ℕ | ∃ k, n = k * 100 + k ∧ 2000 ≤ n ∧ n ≤ 10000} = 80 := by
  have h1 : {n : ℕ | ∃ k, n = k * 100 + k ∧ 2000 ≤ n ∧ n ≤ 10000} = Set.image (fun k => k * 100 + k) (Set.Icc 20 99) := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume n ∈ {n : ℕ | ∃ k, n = k * 100 + k ∧ 2000 ≤ n ∧ n ≤ 10000}
      rintro ⟨k, hk_eq, hk1, hk2⟩
      have hk3 : k ≥ 20 := by 
        omega
      have hk4 : k ≤ 99 := by
        omega
      refine ⟨k, ⟨by omega, by omega⟩, by omega⟩
    · -- Assume n ∈ Set.image (fun k => k * 100 + k) (Set.Icc 20 99)
      rintro ⟨k, ⟨hk3, hk4⟩, hk_eq⟩
      refine ⟨k, by omega, by omega, by omega⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try native_decide