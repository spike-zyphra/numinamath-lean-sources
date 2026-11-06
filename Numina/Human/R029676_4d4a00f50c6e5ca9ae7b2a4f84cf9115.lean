import Mathlib

set_option maxRecDepth 1000 in
/-- 6. (HUN) Five students $A, B, C, D$, and $E$ have taken part in a certain competition. Before the competition, two persons $X$ and $Y$ tried to guess the rankings. $X$ thought that the ranking would be $A, B, C, D, E$; and $Y$ thought that the ranking would be $D, A, E, C, B$. At the end, it was revealed that $X$ didn't guess correctly any rankings of the participants, and moreover, didn't guess any of the orderings of pairs of consecutive participants. On the other hand, $Y$ guessed the correct rankings of two participants and the correct ordering of two pairs of consecutive participants. Determine the rankings of the competition. -/
example (z : Equiv.Perm (Fin 5)) :
    let x : Equiv.Perm (Fin 5) := Equiv.refl _;
    let y : Equiv.Perm (Fin 5) := Equiv.ofBijective (fun i ↦ match i with
      | 0 => 3
      | 1 => 0
      | 2 => 4
      | 3 => 2
      | 4 => 1
    ) (by decide);
    (
      (∀ i, x i ≠ z i) ∧
      (∀ i < 4, ∀ j < 4, ¬(x i = z j ∧ x (i + 1) = z (j + 1))) ∧
      (Finset.card {i | y i = z i} = 2) ∧
      (Finset.card {i | i < 4 ∧ ∃ j < 4, y i = z j ∧ y (i + 1) = z (j + 1)} = 2)
    ) ↔
    (z 0 = 4 ∧ z 1 = 3 ∧ z 2 = 0 ∧ z 3 = 2 ∧ z 4 = 1) := by
  -- The result is $E D A C B$.
  decide +revert
