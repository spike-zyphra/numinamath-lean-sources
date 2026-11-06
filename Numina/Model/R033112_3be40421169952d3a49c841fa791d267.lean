import Mathlib
theorem number_theory_611356 : {n : ℕ | 1 ≤ n ∧ n ≤ 2005 ∧ Nat.factorial n ∣ ∏ i in Finset.range n, (4 * i + 2)}.ncard = 2005:= by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 2005 ∧ Nat.factorial n ∣ ∏ i in Finset.range n, (4 * i + 2)} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 2005 ∧ Nat.factorial n ∣ ∏ i in Finset.range n, (4 * i + 2)) (Finset.Icc 0 2005):= by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide