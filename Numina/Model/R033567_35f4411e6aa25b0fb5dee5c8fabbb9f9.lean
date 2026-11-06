import Mathlib

theorem algebra_25522 :
    IsLeast
    ((fun ⟨a, a'⟩ ↦ a + a') '' {(a, a') : ℕ × ℕ | ∃ c c', a + c ≠ 0 ∧ 12 * a = 5 * (a + c) ∧ a' + c' = 50 ∧
    25 * (a + a') = 11 * (a + c + 50)})
    154 := by
  constructor
  · -- Show 154 is in the image
    simp
    exact ⟨125, 29, ⟨175, by trivial, rfl, ⟨21, rfl⟩, rfl⟩, rfl⟩
  · -- Show it is the minimum
    simp only [lowerBounds, Set.mem_image]
    rintro y ⟨⟨a, a'⟩, ⟨c, c', ha, hb, hc, hd⟩, rfl⟩
    dsimp at ha hb hc hd ⊢
    by_contra h
    push_neg at h
    omega