import Mathlib

theorem number_theory_162325 :
    Set.ncard {k : ℕ | 1 ≤ k ∧ k ≤ 2013 ∧ (k ^ k) % 10 = 1} = 202 := by
  have h1 : {k : ℕ | 1 ≤ k ∧ k ≤ 2013 ∧ (k ^ k) % 10 = 1} = Finset.filter (fun k => 1 ≤ k ∧ k ≤ 2013 ∧ (k ^ k) % 10 = 1) (Finset.Icc 0 2013) := by
    ext k
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide