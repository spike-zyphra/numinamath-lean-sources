import Mathlib

theorem number_theory_182540 :
    Set.ncard {n : ℕ | 2021 ≤ n ∧ n ≤ 9998 ∧ (n % 10) = (n / 10) % 10} = 797 := by
  have h1 : {n : ℕ | 2021 ≤ n ∧ n ≤ 9998 ∧ (n % 10) = (n / 10) % 10} = Finset.filter (λ n => 2021 ≤ n ∧ n ≤ 9998 ∧ (n % 10) = (n / 10) % 10) (Finset.Icc 2021 9998) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide