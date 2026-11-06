import Mathlib

/- In a hat are $1992$ notes with all numbers from $1$ to $1992$. At random way, two bills are drawn simultaneously from the hat; the difference between the numbers on the two notes are written on a new note, which is placed in the hat, while the two drawn notes thrown away. It continues in this way until there is only one note left in it the hat. Show that there is an even number on this slip of paper. -/
theorem negated_number_theory_86530 :
    ∃ (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 1992), 
    ¬ (Even (S.card)) := by 
  -- Choose the initial set to be all 
  use {1}
  -- Automatically solve and show intuition
  decide