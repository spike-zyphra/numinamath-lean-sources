import Mathlib

def isProperNumber (n : ℕ) := 0 < n ∧ 3 ∣ (Nat.digits 3 n).sum

theorem number_theory_318548 :
    ∑ᶠ n ∈ {n | isProperNumber n ∧ n ≤ 2005}, n = 671007 := by
  have h : {n | isProperNumber n ∧ n ≤ 2005} = Finset.filter (fun n => 0 < n ∧ 3 ∣ (Nat.digits 3 n).sum) (Finset.Iic 2005) := by
    ext n
    simp [isProperNumber, Finset.mem_Iic]
    <;> omega
  rw [h]
  rw [finsum_mem_eq_toFinset_sum]
  native_decide