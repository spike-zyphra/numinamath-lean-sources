import Mathlib

theorem algebra_314980 (n : ℕ) (x : Fin n → ℝ)
    (h₀ : ∀ i, x i = -3 ∨ x i = 0 ∨ x i = 1)
    (h₁ : ∑ i, (x i)^2 = 279)
    (h₂ : ∑ i, (x i)^3 = -585) :
    ∑ i, (x i)^4 = 2007 := by
  have eq1 : ∀ i, (x i)^4 = 3 * (x i)^2 - 2 * (x i)^3 := by
    intro i 
    have h : x i = -3 ∨ x i = 0 ∨ x i = 1 := h₀ i
    rcases h with (h | h | h)
    · -- x i = -3
      rw [h]
      norm_num
    · -- x i = 0
      rw [h]
      norm_num 
    · -- x i = 1 
      rw [h]
      norm_num 
  have eq2 : ∑ i, (x i)^4 = ∑ i, (3 * (x i)^2 - 2 * (x i)^3) := by 
    congr
    funext i 
    exact eq1 i 
  rw [eq2]
  have eq3 : ∑ i, (3 * (x i)^2 - 2 * (x i)^3) = 3 * (∑ i, (x i)^2) - 2 * (∑ i, (x i)^3) := by 
    rw [Finset.sum_sub_distrib]
    rw [←Finset.mul_sum, ←Finset.mul_sum]
    all_goals norm_num 
  rw [eq3]
  rw [h₁, h₂]
  all_goals norm_num