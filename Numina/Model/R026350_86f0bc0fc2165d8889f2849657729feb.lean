import Mathlib

def a (n : ℕ) := ∑ i ∈ Finset.range (n + 1), 3 ^ i

theorem number_theory_262878 :
    Set.ncard {x | ∃ n, x = a n ∧ 1 ≤ n ∧ n ≤ 2013 ∧ 7 ∣ x} = 335 := by 
  have h1 : {x | ∃ n, x = a n ∧ 1 ≤ n ∧ n ≤ 2013 ∧ 7 ∣ x} = Finset.filter (fun x => 7 ∣ x) (Finset.image (fun n => a n) (Finset.Icc (1 : ℕ) 2013)) := by
    ext x 
    simp [a]
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide