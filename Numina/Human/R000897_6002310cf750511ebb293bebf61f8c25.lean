import Mathlib

/-The five tallest buildings in Los Angeles in 1985 had a mean height of 733 feet. The tallest of the five buildings has a height of 858 feet, the shortest of the five 625 feet. If a new building were constructed with a height of 885 feet, by how many feet would it increase the mean height of the five tallest buildings of the city?-/
theorem algebra_18930 (h : Fin 5 → ℕ) (h₀ : ∑ i : Fin 5, h i = 733 * 5)
    (h₁ : h 4 = 625) (h₂ : h 0 = 858) :
    ((∑ i : Fin 4, h i) + 885) / (5 : ℝ) - 733 = 52 := by
  -- substitute h₀ : ∑ i : Fin 5, h i = 733 * 5
  suffices h₅ : ((∑ i : Fin 4, h i) + 885) / (5 : ℝ) - (∑ i : Fin 5, h i) / (5 : ℝ) = 52 by
    rw [h₀] at h₅
    norm_num at h₅ ⊢
    exact h₅
  -- just simplify the conclusion and substitute h 4 = 625
  clear h₂
  simp [Finset.sum, Fin.castSucc, Fin.castAdd, Fin.succ]
  ring_nf
  rw [h₁]
  norm_num
