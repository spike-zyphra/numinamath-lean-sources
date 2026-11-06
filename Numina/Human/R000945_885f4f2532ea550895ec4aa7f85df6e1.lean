import Mathlib

/-Captain Rusczyk tracked down a pirate who had stolen $2345_{6}$ dollars worth of goods from his ship. After winning an epic duel, the Captain demands that the pirate return $41324_{5}$ dollars. How much has the pirate gone in debt due to his two encounters with Rusczyk? Express your answer in base 10.-/
theorem number_theory_19294 : Nat.ofDigits 5 [4, 2, 3, 1, 4] - Nat.ofDigits 6 [5, 4, 3, 2] = 2145 := by
  simp [Nat.ofDigits]