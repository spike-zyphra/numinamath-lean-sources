import Mathlib

theorem algebra_15086 : (Nat.card {x | x ∈ Finset.Icc 1 52 ∧ x % 4 = 3}) / 52 = 1 / 4 := by
  have h1 : Nat.card {x | x ∈ Finset.Icc 1 52 ∧ x % 4 = 3} = 13 := by
    have h2 : {x | x ∈ Finset.Icc 1 52 ∧ x % 4 = 3} = Finset.filter (fun x => x % 4 = 3) (Finset.Icc 1 52) := by 
      ext n
      simp 
    rw [h2]
    rw [Nat.card_eq_fintype_card]
    simp
    <;> try { native_decide }
  calc 
    (Nat.card {x | x ∈ Finset.Icc 1 52 ∧ x % 4 = 3}) / 52 = 13 / 52 := by 
      rw [h1]
    _ = 0 := by norm_num
    _ = 1 / 4 := by norm_num