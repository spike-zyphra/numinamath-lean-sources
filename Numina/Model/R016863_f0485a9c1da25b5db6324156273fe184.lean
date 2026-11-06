import Mathlib

theorem algebra_256609 (M N : Set ℕ) (hM : M = {1, 2}) (hN : N = {x | ∃ a ∈ M, x = 2 * a - 1}) :
    M ∩ N = {1} := by

  have h1 : N = {1, 3} := by
    rw [hN]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- Assume h : ∃ a ∈ M, x = 2 * a - 1
      rintro ⟨a, ha, h_eq⟩
      rw [hM] at ha
      simp at ha
      rcases ha with (rfl | rfl)
      · 
        omega
      · 
        omega
    · -- Assume x ∈ {1, 3}
      rintro (rfl | rfl)
      · 
        refine ⟨1, by simp [hM], by omega⟩ 
      · 
        refine ⟨2, by simp [hM], by omega⟩

  rw [h1]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, hM, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume x ∈ M ∩ N
    rintro ⟨hx1, hx2⟩
    omega
  · -- Assume x = 1
    intro hx
    rw [hx]
    constructor
    · -- Show 1 ∈ {1, 2}
      simp
    · -- Show 1 ∈ {1, 3}
      simp