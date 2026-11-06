import Mathlib

theorem algebra_1236 : (Set.ncard {p : Fin 6 × Fin 6 | ∃ x y, p.1 * x + p.2 * y = 1 ∧ 2 * x + y = 3}) / 36 = 11 / 12 := by
  have h1 : {p : Fin 6 × Fin 6 | ∃ x y, p.1 * x + p.2 * y = 1 ∧ 2 * x + y = 3} = Finset.filter (fun p : Fin 6 × Fin 6 => ∃ x y, p.1 * x + p.2 * y = 1 ∧ 2 * x + y = 3) (Finset.univ : Finset (Fin 6 × Fin 6)) := by
    ext p
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide