import Mathlib

theorem number_theory_9652 :
    Set.ncard {x : ℕ | 0 < x ∧ x < 100 ∧ 9 ∣ 2 ^ x + 2} = 16 := by
  have h1 : {x : ℕ | 0 < x ∧ x < 100 ∧ 9 ∣ 2 ^ x + 2} = Finset.filter (λ x => 0 < x ∧ x < 100 ∧ 9 ∣ 2 ^ x + 2) (Finset.range 100) := by
    ext x
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  rfl