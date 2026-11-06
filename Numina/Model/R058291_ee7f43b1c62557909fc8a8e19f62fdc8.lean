import Mathlib

theorem algebra_97883 (S : Finset ℤ) (hS : S = {-16, -4, 0, 2, 4, 12}) :
    IsGreatest {x | ∃ a ∈ S, ∃ b ∈ S, x = a - b} 28 := by
  rw [hS]
  constructor
  · -- Let's prove that $28$ is achievable by providing the witness.
    use 12, by simp, -16, by simp
    all_goals omega
  · -- Let's prove that $28$ is the greatest element
    intro x hx
    rcases hx with ⟨a, ha, b, hb, hx⟩
    fin_cases ha <;> fin_cases hb <;> omega