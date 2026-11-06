import Mathlib

def A : Set ℕ := {1, 3, 5, 7}
def B : Set ℕ := {2, 4, 6, 8, 20}
def C : Set ℕ := {x | ∃ a b, x = a + b ∧ a ∈ A ∧ b ∈ B}

theorem algebra_300322 : C.ncard = 11 := by
  have h1 : C = {3, 5, 7, 9, 11, 13, 15, 21, 23, 25, 27} := by 
    ext x
    simp only [C, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x ∈ C; prove x ∈ {3, 5, 7, 9, 11, 13, 15, 21, 23, 25, 27}
      rintro ⟨a, b, h_eq, ha, hb⟩
      have ha1 : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7 := by
        simp [A] at ha
        omega
      have hb1 : b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 8 ∨ b = 20 := by
        simp [B] at hb
        omega
      rcases ha1 with (rfl | rfl | rfl | rfl) <;> rcases hb1 with (rfl | rfl | rfl | rfl | rfl) <;> simp [h_eq] at *
    · -- Assume x ∈ {3, 5, 7, 9, 11, 13, 15, 21, 23, 25, 27}; prove x ∈ C
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 3
        exact ⟨1, 2, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 5
        exact ⟨1, 4, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 7
        exact ⟨1, 6, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 9
        exact ⟨1, 8, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 11
        exact ⟨3, 8, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 13
        exact ⟨5, 8, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 15
        exact ⟨7, 8, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 21
        exact ⟨1, 20, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 23
        exact ⟨3, 20, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 25
        exact ⟨5, 20, by norm_num, by simp [A], by simp [B]⟩
      · -- x = 27
        exact ⟨7, 20, by norm_num, by simp [A], by simp [B]⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp