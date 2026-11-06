import Mathlib

/- sign x = -1, 0, or 1 -/
lemma sign_cases {x:ℝ}:
  SignType.sign x = -1 ∨ SignType.sign x = 0 ∨ SignType.sign x = 1 := by
  dsimp [SignType.sign]
  aesop

/- if a set contain ≥ 4 real numbers, then at least two of them have same sign. -/
lemma exists_two_pos_or_two_neg_of_four_le_card
  {A: Finset ℝ} (hA: A.card ≥ 4):
  ∃ x y, x ≠ y ∧ x ∈ A ∧ y ∈ A ∧ ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) := by
  have h1: ({-1,0,1}: Finset SignType).card < A.card := by
    have: ({-1,0,1}: Finset SignType).card = 3 := by simp
    linarith only [this, hA]
  have h2: ∀ x ∈ A, SignType.sign x ∈ ({-1,0,1}: Finset SignType) := by
    intro x _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using sign_cases
  have h3 := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h1 h2
  rcases h3 with ⟨x, hx, y, hy, xney, hxy⟩
  use x,y,xney,hx,hy
  rcases (@sign_cases x) with (hhx | hhx | hhx)
  any_goals
    rw [hhx] at hxy
    simp only [← sign_eq_one_iff, hhx, SignType.neg_eq_self_iff, one_ne_zero, hxy.symm, and_self, ←
    sign_eq_neg_one_iff, or_self, or_true, true_or]
  symm at hxy
  rw [sign_eq_zero_iff] at hhx hxy
  simp [hhx, hxy] at xney


/- 1. Let $A$ be a finite set, for any $x, y \in A$, if $x \neq y$, then $x+y \in A$.
Then, the maximum number of elements in $A$ is $\qquad$ . -/
theorem algebra_325842:
  IsGreatest {u:ℕ | ∃ (A: Finset ℝ), u = A.card ∧
    ∀(x y), x ∈ A → y ∈ A → x ≠ y → x+y ∈ A } 3 := by

  rw [IsGreatest, upperBounds]
  simp only [ne_eq, Set.mem_setOf_eq, forall_exists_index, and_imp]

  constructor

  · -- {-1,0,1} witness 3 is attainable.
    use {-1,0,1}
    refine ⟨(by norm_num), ?_⟩
    aesop

  · rintro _ A rfl h
    -- suppose on the contrary
    by_contra hA
    replace hA: A.card ≥ 4 := by
      push_neg at hA
      exact hA
    have Anz: A.Nonempty := by
      by_contra!
      replace: A.card = 0 := by
        refine Finset.card_eq_zero.mpr ?_
        exact Finset.not_nonempty_iff_eq_empty.mp this
      norm_num [this] at hA
    -- then exist two elements of same sign
    have := exists_two_pos_or_two_neg_of_four_le_card hA
    rcases this with ⟨x, y, xney, hx, hy, h⟩
    rcases h with (⟨xpos, ypos⟩ | ⟨xneg, yneg⟩)
    
    -- either case A is unbounded, contradiction.
    · rcases (Finset.max_of_nonempty Anz) with ⟨s, hs⟩
      by_cases hhx: x = s
      · specialize h x y hx hy xney
        rw [← hhx] at hs
        have h1: x+y ≤ x := by
          exact Finset.le_max_of_eq h hs
        have h2: x+y > x := by linarith only [ypos]
        linarith only [h1, h2]
      · specialize h x s hx (Finset.mem_of_max hs) hhx
        have: x+s ≤ s := Finset.le_max_of_eq h hs
        linarith only [this, xpos]
    · rcases (Finset.min_of_nonempty Anz) with ⟨s,hs⟩
      by_cases hhx: x = s
      · specialize h x y hx hy xney
        rw [← hhx] at hs
        have h1: x ≤ x+y := by
          exact Finset.min_le_of_eq h hs
        have h2: x+y < x := by linarith only [yneg]
        linarith only [h1, h2]
      · specialize h x s hx (Finset.mem_of_min hs) hhx
        have: s ≤ x + s := Finset.min_le_of_eq h hs
        linarith only [this, xneg]