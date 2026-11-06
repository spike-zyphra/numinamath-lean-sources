import Mathlib

theorem algebra_20474 : (Nat.card (Finset.Icc 1 25) ^ 3) = 15625 := by
  have h1 : Nat.card (Finset.Icc 1 25) = 25 := by
    simp [Finset.Icc]
    <;> try { native_decide }
  calc
    Nat.card (Finset.Icc 1 25) ^ 3 = 25 ^ 3 := by rw [h1]
    _ = 15625 := by norm_num