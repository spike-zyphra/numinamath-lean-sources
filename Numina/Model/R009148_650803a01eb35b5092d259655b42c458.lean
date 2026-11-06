import Mathlib

theorem number_theory_15935 : {n : ℕ | n ∈ Finset.Icc 1 200 ∧ n ≡ 1 [MOD 9]}.ncard = 23 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 200 ∧ n ≡ 1 [MOD 9]} = Finset.filter (fun n => n ≡ 1 [MOD 9]) (Finset.Icc 1 200) := by
    ext n
    simp [Finset.mem_Icc]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide