import Mathlib

theorem algebra_96407 (a : Fin 5 → ℕ) (ha : ∑ i, a i = 5 * 30) (h : 18 ∈ Set.range a) :
    (5 - 1) * 33 = ∑ i, a i - 18 := by 
  have h1 : ∑ i, a i = 150 := by 
    norm_num at ha ⊢ 
    all_goals omega 
  calc
    (5 - 1) * 33 = 132 := by norm_num 
    _ = 150 - 18 := by norm_num 
    _ = ∑ i, a i - 18 := by 
      rw [h1]