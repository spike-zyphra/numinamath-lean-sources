import Mathlib

theorem number_theory_197553 : {x | ∃ n, x = n ∧ n ≤ 1000 ∧ (Nat.divisors n).card ≡ 1 [MOD 2]}.encard = 31 := by
  have h1 : {x | ∃ n, x = n ∧ n ≤ 1000 ∧ (Nat.divisors n).card ≡ 1 [MOD 2]} = Finset.filter (fun n => (Nat.divisors n).card ≡ 1 [MOD 2]) (Finset.Iic 1000) := by
    ext n
    simp [Nat.ModEq]
    <;> try tauto
    <;> try omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide