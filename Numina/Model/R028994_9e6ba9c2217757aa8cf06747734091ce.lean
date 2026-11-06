import Mathlib

theorem algebra_20765 : (1 : ℝ) / 6 = {x : Fin 6 × Fin 6 | x.1 = x.2}.ncard / (6 * 6) := by 
  have h1 : {x : Fin 6 × Fin 6 | x.1 = x.2}.ncard = 6 := by
    simp [Set.ncard_eq_toFinset_card']
    <;> native_decide
  rw [h1]
  norm_num