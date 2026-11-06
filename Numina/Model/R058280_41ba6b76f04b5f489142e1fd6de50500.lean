import Mathlib

theorem number_theory_272776 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) = n ∧ 4 ∣ n}.ncard = 20 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) = n ∧ 4 ∣ n} = Finset.filter (λ n => (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) = n ∧ 4 ∣ n) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide