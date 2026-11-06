import Mathlib

theorem number_theory_7021 : {x : ℕ | x.gcd 15 = 1 ∧ x = 4 ∨ x = 8 ∨ x = 16 ∨ x = 28 ∨ x = 32 ∨ x = 44 ∨ x = 52 ∨ x = 56}.encard = 8 := by
  have : {x : ℕ | x.gcd 15 = 1 ∧ x = 4 ∨ x = 8 ∨ x = 16 ∨ x = 28 ∨ x = 32 ∨ x = 44 ∨ x = 52 ∨ x = 56} = {4, 8, 16, 28, 32, 44, 52, 56} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume that $x \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$. Then $x \in \{4, 8, 16, 28, 32, 44, 52, 56\}$.
      intro h
      rcases h with (⟨hx1, hx2⟩ | hx2 | hx3 | hx4 | hx5 | hx6 | hx7 | hx8)
      · -- Case $x.gcd\ 15 = 1 \land x = 4$. Then $x = 4$.
        have h4 : x = 4 := hx2
        simp [h4]
      · -- Case $x = 8$. Then $x \in \{4, 8, 16, 28, 32, 44, 52, 56\}$.
        simp [hx2]
      · -- Case $x = 16$. Then $x \in \{4, 8, 16, 28, 32, 44, 52, 56\}$.
        simp [hx3]
      · -- Case $x = 28$. Then $x \in \{4, 8, 16, 28, 32, 44, 52, 56\}$.
        simp [hx4]
      · -- Case 32. Then x in the right side bne set.
        simp [hx5]
      · -- Case 44. Then x in the right side bne set.
        simp [hx6]
      · -- Case 52. Then x in the right side bne set.
        simp [hx7]
      · -- Case 56. Then x in the right side bne set.
        simp [hx8]
    · -- Assume $x \in \{4, 8, 16, 28, 32, 44, 52, 56\}$, then $x \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$.
      intro hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case x = 4. Then $4 \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$.
        left
        constructor
        · -- Show that gcd(4,15) = 1
          norm_num
        all_goals
          norm_num
      · -- Case x = 8. Then $8 \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$.
        right
        left
        norm_num
      · -- Case x = 16. Then $16 \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$.
        right
        right
        left
        norm_num
      · -- Case x = 28. Then $28 \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$.
        right
        right
        right
        left
        norm_num
      · -- Case x = 32. Then $32 \in \{x \mid x.gcd\ 15 = 1 \land x = 4 \lor x = 8 \lor x = 16 \lor x = 28 \lor x = 32 \lor x = 44 \lor x = 52 \lor x = 56\}$.
        right
        right
        right
        right
        left
        norm_num
      · -- Case x = 44. Then 44 is in the right side of the condition.
        right
        right
        right
        right
        right
        left
        norm_num
      · -- Case x = 52. Then 52 is in the right side of the condition.
        right
        right
        right
        right
        right
        right
        left
        norm_num
      · -- Case x = 56. Then 56 is in the right side of the condition.
        right
        right
        right
        right
        right
        right
        right
        norm_num
  rw [this]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }