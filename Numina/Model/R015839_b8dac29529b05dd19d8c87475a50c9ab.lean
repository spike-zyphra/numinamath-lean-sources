import Mathlib

def f (a b : Fin 4) := (a + b) % 4

theorem algebra_302300 {S : Finset (Fin 4)} (hS : S = {0, 1, 2, 3}) :
    {x | (f x x) + 2 ≡ 0 [ZMOD 4]}.ncard = 2 := by
  have h1 : {x | (f x x) + 2 ≡ 0 [ZMOD 4]} = {1, 3} := by
    ext x
    simp [f, Finset.mem_insert, Finset.mem_singleton]
    fin_cases x <;> simp [Int.ModEq] at *
    <;> tauto
  rw [h1]
  rw [Set.ncard_pair]
  all_goals simp