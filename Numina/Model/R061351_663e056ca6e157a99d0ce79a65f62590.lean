import Mathlib

def S : ℕ → ℕ
| n => ∑ i in Finset.Icc 1 n, i

theorem number_theory_110949 :
    Set.ncard {i | 1 ≤ i ∧ i ≤ 2015 ∧ 2015 ∣ S i} = 8 := by
  have h1 : {i | 1 ≤ i ∧ i ≤ 2015 ∧ 2015 ∣ S i} = Finset.filter (fun i => 1 ≤ i ∧ i ≤ 2015 ∧ 2015 ∣ S i) (Finset.Icc 0 2015) := by
    ext n
    simp [Finset.mem_Icc]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide