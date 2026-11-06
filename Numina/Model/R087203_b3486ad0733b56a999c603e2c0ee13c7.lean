import Mathlib

theorem number_theory_208122 (n : ℕ) (hn : n = 180) :
    IsLeast {x | ∃ s : Finset ℕ, s.card = n ∧ x = (1 / (2 * 3 ^ 59))} (1 / (2 * 3 ^ 59)) := by 
  rw [hn]
  constructor
  · -- Show that the element is in the set.
    use Finset.Icc 0 179
    all_goals native_decide
  · -- Show that it's the smallest element.
    intro x hx
    rcases hx with ⟨s, hs_card, hx⟩
    have : x = 1 / (2 * 3 ^ 59) := hx
    linarith