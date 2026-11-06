import Mathlib

/- By inserting parentheses, it is possible to give the expression 2×3+4×5 several values.  
How many different values can be obtained?
(A) 2
(B) 3
(C) 4
(D) 5
(E) 6 -/
theorem algebra_93868 : {x : ℕ | x = (2 * 3) + 4 * 5 ∨ x = (2 * 3) + (4 * 5) ∨ x = 2 * (3 + 4) * 5 ∨ x = 2 * 3 + (4 * 5) ∨ x = (2 * 3 + 4) * 5 ∨ x = ((2 * 3) + 4) * 5 ∨ x = (2 * (3 + 4)) * 5 ∨ x = 2 * (3 + 4 * 5) ∨ x = 2 * ((3 + 4) * 5)∨ x = 2 * (3 + (4 * 5))}.ncard = 4 := by
  simp
  --prove that the set in the problem is the same as {26,46,50,70}
  have j : ({x | x = 26 ∨ x = 70 ∨ x = 26 ∨ x = 50 ∨ x = 70 ∨ x = 46 ∨ x = 70 ∨ x = 46} : Set ℕ) = ({26, 46, 50, 70} : Finset ℕ) := by 
    ext x
    constructor
    · simp
      intro h
      obtain h1|h2|h3|h4|h5|h6|h7|h8 := h
      · left
        exact h1
      · right
        right
        right
        exact h2
      · left
        exact h3
      · right
        right
        left
        exact h4
      · right
        right
        right
        exact h5
      · right
        left
        exact h6
      · right
        right
        right
        exact h7
      · right
        left
        exact h8
    · simp
      intro h
      obtain h1|h2|h3|h4 := h
      · left
        exact h1
      · right
        right
        right
        right
        right
        left
        exact h2
      · right
        right
        right
        left
        exact h3
      · right
        left
        exact h4
  --than the cardinalities of the two sets are the same, and in particular are 4
  rw[j, Set.ncard_eq_toFinset_card']
  simp