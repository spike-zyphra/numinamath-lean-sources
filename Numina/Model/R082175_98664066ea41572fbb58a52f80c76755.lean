import Mathlib

def f : ℕ → ℕ
| 0 => 101
| n + 1 => (f n) * 10 + 1

theorem number_theory_96897 :
    Set.ncard {i | 101 ∣ f i ∧ i < 2018} = 505 := by 
  have h1 : {i | 101 ∣ f i ∧ i < 2018} = Finset.filter (fun i => 101 ∣ f i ∧ i < 2018) (Finset.Icc (0 : ℕ) 2017) := by 
    ext i
    simp 
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide