import Mathlib

def digitSum (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_240112 : Set.ncard {x | ∃ n, x = digitSum n ∧ n ∈ Finset.Icc 1 2021} = 28 := by 
  have h1 : {x | ∃ n, x = digitSum n ∧ n ∈ Finset.Icc 1 2021} = Finset.image (λ n => digitSum n) (Finset.Icc 1 2021) := by
    ext x
    simp 
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide