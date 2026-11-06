import Mathlib

theorem number_theory_206910 :
    Set.ncard {d : ℕ | d ∣ Nat.factorial 11 ∧ 3 ∣ d} = 432 := by
  have h1 : Nat.factorial 11 = 39916800 := rfl
  have : {d : ℕ | d ∣ Nat.factorial 11 ∧ 3 ∣ d} = Finset.filter (λ d => 3 ∣ d) (Nat.divisors (Nat.factorial 11)) := by
    ext d
    simp
    <;> tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  rw [h1]
  native_decide