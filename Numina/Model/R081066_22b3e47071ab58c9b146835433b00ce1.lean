import Mathlib

theorem number_theory_215366 (a b : Fin 50 → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ j, b j ≠ 0) (hij : ∀ i j, a i + b j ≠ 0)
    (hdist : ∀ i j, a i = a j ∨ b i = b j → i = j)
    (hrrat : {x | ∃ i j, x = a i + b j ∧ ∃ q : ℚ, x = q}.encard = 50) :
    {x | ∃ i j, x = a i + b j ∧ ∃ q : ℚ, x = q}.encard ≤ 1250 := by 
  rw [hrrat]
  all_goals norm_num [Set.encard]
  all_goals try { linarith }
  all_goals contradiction
  all_goals try { linarith }
  all_goals contradiction