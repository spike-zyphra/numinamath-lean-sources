import Mathlib

theorem number_theory_33120 : {x : ℤ | x ∈ Finset.Ico 0 30 ∧ x^4 + 2 * x^3 + 3 * x^2 - x + 1 ≡ 0 [ZMOD 30]}.ncard = 1 := by
  have h1 : {x : ℤ | x ∈ Finset.Ico 0 30 ∧ x^4 + 2 * x^3 + 3 * x^2 - x + 1 ≡ 0 [ZMOD 30]} = 
    Finset.filter (fun x => x^4 + 2 * x^3 + 3 * x^2 - x + 1 ≡ 0 [ZMOD 30]) (Finset.Ico (0 : ℤ) 30) := by
    ext x
    simp [Finset.mem_filter, Finset.mem_Ico]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide