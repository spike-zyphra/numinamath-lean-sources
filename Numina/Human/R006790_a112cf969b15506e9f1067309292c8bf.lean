import Mathlib

/-Let $K$ be an odd positive integer. Philippe and Emmanuel are faced with $2K$ cards numbered from $1$ to $2K$. Taking turns, they each take one of the cards in front of them and add it to their hand, until there are no more cards in front of them. (So each player takes $K$ cards.) At that point, they each calculate the sum of the numbers in their hand. The one who has an even sum wins. Philippe starts.
Show that Philippe wins if $K \equiv 1 \pmod 4$, and Emmanuel wins if $K \equiv 3 \pmod 4$.-/

theorem nubmer_theory_641164 (K : ℕ) (hK_odd : Odd K) :
    if K % 4 = 1 then
      -- Philippe has a winning strategy.
      -- If P starts with an Even card, the two possible outcomes for p_o that E can force are
      -- (K-1)/2 (E-battle) and 0 (P gets E-cards).
      -- We prove both of these are even, so P wins by picking an Even card first.
      Even ((K - 1) / 2) ∧ Even 0
    else
      -- Emmanuel has a winning strategy.
      -- If P starts with an Even card, E can force p_o = (K-1)/2. We prove this is odd.
      -- If P starts with an Odd card, E can force p_o = K. We prove this is odd.
      -- Since E can always force an odd p_o, E wins.
      Odd ((K - 1) / 2) ∧ Odd K := by

  by_cases hK_mod_4 : K % 4 = 1

  · simp only [hK_mod_4, if_true]
    constructor
    · rw [Nat.even_div]
      omega
    · exact even_zero

  · simp only [hK_mod_4, if_false]
    constructor
    · have h_K_mod_4_eq_3 : K % 4 = 3 := by 
        suffices K % 4 ≠ 2 ∧ K % 4 ≠ 0 by
          omega
        simp[Nat.odd_iff] at hK_odd
        omega
      rw [Nat.odd_iff]
      omega
    · exact hK_odd
