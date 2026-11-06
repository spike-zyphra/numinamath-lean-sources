import Mathlib

/- How many zeroes are at the end of $42!$ (42 factorial)?  (Reminder: The number $n!$ is the product of the integers from 1 to $n$.  For example, $5!=5\cdot 4\cdot3\cdot2\cdot 1= 120$.) -/
theorem algebra_18759 : (Nat.factorial 42) % 10^9 = 0 ∧ (Nat.factorial 42) % 10^10 ≠ 0 := by 
  constructor
  · rfl
  · have : (Nat.factorial 42) % 10^10 = 4 * 10^9 := by rfl
    rw [this]
    simp