import Mathlib

theorem algebra_97456 (S : Finset ℤ) (hS : S = {-3, -2, -1, 4, 5}) :
    IsGreatest {x | ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = a * b * c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S} 30 := by
  rw [hS]
  constructor
  · -- Show that 30 is indeed achievable, through the numbers -3, -2, 5
    use -3, -2, 5
    norm_num
    <;> tauto
  · -- We need to prove that given three distinct elements from the set, the product is at most 30
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hmul, ha2, hb2, hc2⟩
    fin_cases ha2 <;> fin_cases hb2 <;> fin_cases hc2 <;> omega