import Mathlib

theorem number_theory_246902 :
    Set.ncard {k : ℕ | 0 ≤ k ∧ k ≤ 2188 ∧ 2188 ∣ Nat.choose 2188 k} = 2146 := by
  have h1 : {k : ℕ | 0 ≤ k ∧ k ≤ 2188 ∧ 2188 ∣ Nat.choose 2188 k} = Finset.filter (λ k => 0 ≤ k ∧ k ≤ 2188 ∧ 2188 ∣ Nat.choose 2188 k) (Finset.Icc 0 2188) := by
    ext k
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide