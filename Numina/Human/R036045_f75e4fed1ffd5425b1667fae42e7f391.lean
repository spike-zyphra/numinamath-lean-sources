import Mathlib

/- Using the letters $A$ and $B$, the following two-letter code words can be formed: $AA$, $AB$, $BB$, $BA$. Using the letters $A$, $B$, and $C$, how many different three-letter code words can be formed?-/
theorem algebra_21716 (alphabet : Set Char) (ha : alphabet = {'A', 'B', 'C'}) :
    (Set.univ : Set (alphabet × alphabet × alphabet)).ncard = 27 := by
  -- Make a tree-diagram for all three-letter code words starting with $A$.
  -- Each path from the top to the bottom contains 3 letters,
  -- which is one of the code words beginning with $A$.
  -- There are 9 such code words.
  -- Clearly, there are 9 code words starting with $B$ and 9 starting with $C$.
  -- In all, there are $\boxed{27}$ code words.
  have : alphabet.Finite := by simp [ha]
  have : Fintype alphabet := this.fintype
  have alphabet_card : Fintype.card alphabet = 3 := by simp [ha]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_univ, Finset.card_univ,
    Fintype.card_prod, Fintype.card_prod, alphabet_card]
