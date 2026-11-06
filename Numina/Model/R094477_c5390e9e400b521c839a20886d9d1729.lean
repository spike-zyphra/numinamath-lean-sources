import Mathlib

theorem number_theory_6353 :
    ∑ᶠ a ∈ {x : ℕ | 1 ≤ x ∧ x ≤ 2020 ∧ 3 ^ x ≡ 9 [MOD 13]}, a = 679730 := by
  have h1 : {x : ℕ | 1 ≤ x ∧ x ≤ 2020 ∧ 3 ^ x ≡ 9 [MOD 13]} = Finset.filter (λ x => 1 ≤ x ∧ x ≤ 2020 ∧ 3 ^ x ≡ 9 [MOD 13]) (Finset.Icc 0 2020) := by
    ext x
    simp [Nat.ModEq]
    <;> omega
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  native_decide