import Mathlib

def is_composite (n : ℕ) := n ≠ 1 ∧ ¬n.Prime

def is_twin_5_composite (n : ℕ) := is_composite n ∧ is_composite (n + 1) ∧ is_composite (n + 2) ∧ is_composite (n + 3) ∧ is_composite (n + 4)

theorem number_theory_302346 :
    Set.ncard {n | n ≤ 100 ∧ is_twin_5_composite n} = 10 := by
  have h1 : {n | n ≤ 100 ∧ is_twin_5_composite n} = Finset.filter (fun n => 
    (n ≤ 100) ∧ (n ≠ 1 ∧ ¬n.Prime) ∧ 
    ( (n + 1) ≠ 1 ∧ ¬(n + 1).Prime ) ∧ 
    ( (n + 2) ≠ 1 ∧ ¬(n + 2).Prime ) ∧ 
    ( (n + 3) ≠ 1 ∧ ¬(n + 3).Prime ) ∧ 
    ( (n + 4) ≠ 1 ∧ ¬(n + 4).Prime )
  ) (Finset.Icc (0 : ℕ) 100) := by
    ext n
    simp [is_twin_5_composite, is_composite]
    all_goals omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide