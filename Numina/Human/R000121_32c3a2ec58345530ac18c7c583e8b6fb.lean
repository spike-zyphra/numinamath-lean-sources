import Mathlib

/-
A troop of 17 monkeys stores their bananas in eleven piles of equal size,
with a twelfth pile containing six bananas left over.
When they divide the total number of bananas into 17 equal groups,
none are left over. What is the smallest number of bananas they can have?
-/
theorem number_theory_4702 : IsLeast {x : ℕ | x % 17 = 0 ∧ ∃ k, x = 11*k + 6} 17 := by
  constructor
  -- check 17 is a possible solution
  · simp_all
  -- check 17 is the least solution
  · dsimp [lowerBounds]
    intro a h
    rcases h with ⟨ha,k,hak⟩
    cases k with
    | zero => simp_all -- impossible
    | succ n => simp_all
