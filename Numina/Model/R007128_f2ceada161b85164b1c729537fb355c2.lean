import Mathlib

theorem algebra_35871 {f g : ℝ → ℝ}
    (hf : f 1 = 3 ∧ f 3 = 7 ∧ f 5 = 9 ∧ f 7 = 13 ∧ f 9 = 17)
    (hg : g 1 = 54 ∧ g 3 = 9 ∧ g 5 = 25 ∧ g 7 = 19 ∧ g 9 = 44) :
    f (g 3) = 17 := by 
        rcases hf with ⟨hf1, hf3, hf5, hf7, hf9⟩
        rcases hg with ⟨hg1, hg3, hg5, hg7, hg9⟩
        rw [hg3]
        rw [hf9]