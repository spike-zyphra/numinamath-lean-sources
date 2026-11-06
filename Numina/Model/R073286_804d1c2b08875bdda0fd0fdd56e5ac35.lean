import Mathlib

theorem number_theory_277683 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 3 ∣ n ∧ 4 ∣ n ∧ (n / 10) % 10 > (n % 10) % 10} = 4 := by
  have : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 3 ∣ n ∧ 4 ∣ n ∧ (n / 10) % 10 > (n % 10) % 10} = Finset.filter (fun (n: ℕ) => 3 ∣ n ∧ 4 ∣ n ∧ (n / 10) % 10 > (n % 10) % 10) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide