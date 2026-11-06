import Mathlib

theorem number_theory_327774 : {(3, 2), (17, 12)} ⊆ {(x, y) : ℤ × ℤ | x^2 - 2 * y^2 = 1} := by 
  intro p hp
  simp at hp ⊢
  rcases hp with (h | h)
  · -- Case where p = (3, 2)
    rcases h with ⟨rfl, rfl⟩
    norm_num
  · -- Case where p = (17, 12)
    rcases h with ⟨rfl, rfl⟩
    norm_num