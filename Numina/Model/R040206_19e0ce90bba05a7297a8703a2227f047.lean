import Mathlib

theorem algebra_21755 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100000000 999999999 ∧ (n / 100000000) % 10 ≠ 0} = 900000000 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100000000 999999999 ∧ (n / 100000000) % 10 ≠ 0} = (Finset.Icc 100000000 999999999 : Set ℕ) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  <;> native_decide