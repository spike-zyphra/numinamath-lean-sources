import Mathlib

theorem number_theory_131653 :
    Set.ncard {n : ℕ | 0 < n ∧ (5 ∣ n ∨ 7 ∣ n) ∧ n ≤ 1000} = 314 := by
  have h1 : {n : ℕ | 0 < n ∧ (5 ∣ n ∨ 7 ∣ n) ∧ n ≤ 1000} = Finset.filter (λ n => 0 < n ∧ (5 ∣ n ∨ 7 ∣ n) ∧ n ≤ 1000) (Finset.Icc 0 1000) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide