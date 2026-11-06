import Mathlib

def A : Set ℕ := {1, 2, 3}
def X : Set ℕ := {x | ∃ a b, x = 4 * a + b ∧ a ∈ A ∧ b ∈ A}
def Y : Set ℕ := {x | ∃ a b, x = 4 * a - b ∧ a ∈ A ∧ b ∈ A}

theorem algebra_122421 : ∑ᶠ x ∈ X ∩ Y, x = 48 := by
  have h1 : X ∩ Y = {5, 6, 7, 9, 10, 11} := by
    ext n
    simp only [X, Y, A, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · -- Assume h: n ∈ X ∩ Y, prove n ∈ {5, 6, 7, 9, 10, 11}
      rintro ⟨⟨a, b, h1, ha, hb⟩, ⟨c, d, h2, hc, hd⟩⟩
      rcases ha with (rfl | rfl | rfl)
      all_goals
        rcases hb with (rfl | rfl | rfl)
        all_goals
          rcases hc with (rfl | rfl | rfl)
          all_goals
            rcases hd with (rfl | rfl | rfl)
            all_goals
              omega
    · -- Assume n ∈ {5, 6, 7, 9, 10, 11}, prove n ∈ X ∩ Y
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show 5 ∈ X ∩ Y
        constructor
        · -- Show 5 ∈ X
          refine ⟨1, 1, by norm_num, by simp, by simp⟩
        · -- Show 5 ∈ Y
          refine ⟨2, 3, by norm_num, by simp, by simp⟩
      · -- Show 6 ∈ X ∩ Y
        constructor
        · -- Show 6 ∈ X
          refine ⟨1, 2, by norm_num, by simp, by simp⟩
        · -- Show 6 ∈ Y
          refine ⟨2, 2, by norm_num, by simp, by simp⟩
      · -- Show 7 ∈ X ∩ Y
        constructor
        · -- Show 7 ∈ X
          refine ⟨1, 3, by norm_num, by simp, by simp⟩
        · -- Show 7 ∈ Y
          refine ⟨2, 1, by norm_num, by simp, by simp⟩
      · -- Show 9 ∈ X ∩ Y
        constructor
        · -- Show 9 ∈ X
          refine ⟨2, 1, by norm_num, by simp, by simp⟩
        · -- Show 9 ∈ Y
          refine ⟨3, 3, by norm_num, by simp, by simp⟩
      · -- Show 10 ∈ X ∩ Y
        constructor
        · -- Show 10 ∈ X
          refine ⟨2, 2, by norm_num, by simp, by simp⟩
        · -- Show 10 ∈ Y
          refine ⟨3, 2, by norm_num, by simp, by simp⟩
      · -- Show 11 ∈ X ∩ Y
        constructor
        · -- Show 11 ∈ X
          refine ⟨2, 3, by norm_num, by simp, by simp⟩
        · -- Show 11 ∈ Y
          refine ⟨3, 1, by norm_num, by simp, by simp⟩
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> try { native_decide }