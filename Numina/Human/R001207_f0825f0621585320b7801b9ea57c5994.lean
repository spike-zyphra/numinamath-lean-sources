import Mathlib

/- Yann and Camille go to a restaurant.  If there are 10 items on the menu, and each orders one dish, how many different combinations of meals can Yann and Camille order if they refuse to order the same dish? (It does matter who orders what---Yann ordering chicken and Camille ordering fish is different from Yann ordering fish and Camille ordering chicken.) -/
theorem algebra_21357 : {p : Fin 2 → Fin 10 | p 0 ≠ p 1}.encard = 90 := by 
  simp [Set.encard]
  rfl