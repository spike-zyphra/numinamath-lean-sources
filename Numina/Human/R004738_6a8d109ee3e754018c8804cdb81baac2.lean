import Mathlib

open Finset

/- Let $S$ be a subset of $\{1,2,3, \cdots, 50\}$ with the following property: the sum of any two distinct elements of $S$ is not divisible by 7. Then, the maximum number of elements in $S$ is 23.
(43rd American High School School Examination) -/
theorem number_theory_313405 :
    IsGreatest {N | ∃ S ⊆ Icc 1 50, #S = N ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬(7 ∣ x + y)} 23 := by
  constructor
  . simp
    use insert 7 ((Icc 1 50).filter (· % 7 ∈ Icc 1 3))
    decide
  . simp [upperBounds]
    intro N S h1 h2 h
    subst N
    -- Divide $A=\\{1,2,3, \\cdots, 50\\}$ into 7 subsets: $A\_{0}, A\_{1}, A\_{2}, A\_{3}, A\_{4}, A\_{5}, A\_{6}$, where the elements of $A\_{i}$ have a remainder of $i$ when divided by 7
    let A (n : ℕ) := S.filter (· % 7 = n)
    have h_union : S = A 0 ∪ A 1 ∪ A 2 ∪ A 3 ∪ A 4 ∪ A 5 ∪ A 6 := by
      ext a
      constructor
      . intro h
        let r := a % 7
        have : r < 7 := by omega
        simp [A]
        interval_cases h1 : r <;> tauto
      . simp [A]
        rintro (h|h|h|h|h|h|h) <;> tauto
    -- $S$ can contain at most one element from $A\_{0}$.
    have h_card_A0 : #(A 0) ≤ 1 := by
      by_contra! h1
      obtain ⟨t, h1, h2⟩ := exists_subset_card_eq (Nat.succ_le_of_lt h1)
      rw [card_eq_two] at h2
      obtain ⟨x, y, hne, h2⟩ := h2
      simp [h2, A, Subset] at h1
      specialize h x (by tauto) y (by tauto) hne
      omega
    -- $A\_{1}$ contains 8 elements
    have h_card_A1 : #(A 1) ≤ 8 := by
      have := filter_subset_filter (· % 7 = 1) h1
      have := card_le_card this
      have : #((Icc 1 50).filter (· % 7 = 1)) = 8 := by
        native_decide
      simp [A]
      linarith
    -- and each of the other subsets contains 7 elements.
    have h_card_A2_to_A6 (n : ℕ) (h : n ∈ Icc 2 6 := by simp) : #(A n) ≤ 7 := by
      have := filter_subset_filter (· % 7 = n) h1
      have := card_le_card this
      simp at h
      obtain ⟨h1, h2⟩ := h
      interval_cases h : n
      all_goals
      have : #((Icc 1 50).filter (· % 7 = n)) = 7 := by
        subst n
        native_decide
      subst n
      simp [A]
      linarith
    have h_counterpart (n : ℕ) (hn : n ∈ Icc 1 3 := by simp) : A n = ∅ ∨ A (7 - n) = ∅ := by
      by_contra! h
      obtain ⟨h1, h2⟩ := h
      rw [←nonempty_iff_ne_empty] at h1 h2
      obtain ⟨x, h1⟩ := Nonempty.exists_mem h1
      obtain ⟨y, h2⟩ := Nonempty.exists_mem h2
      simp [A] at *
      specialize h x (by tauto) y (by tauto) (by omega)
      omega
    -- Moreover, $S$ cannot contain elements from both $A\_{1}$ and $A\_{6}$
    have h_card_A1_A6 : #(A 1) + #(A 6) ≤ 8 := by
      rcases h_counterpart 1 with (h | h)
      . simp [h]
        specialize h_card_A2_to_A6 6
        linarith
      . simp [h]
        linarith
    -- or from both $A\_{2}$ and $A\_{5}$.
    have h_card_A2_A5 : #(A 2) + #(A 5) ≤ 7 := by
      rcases h_counterpart 2 with (h | h)
      . simp [h]
        specialize h_card_A2_to_A6 5
        linarith
      . simp [h]
        specialize h_card_A2_to_A6 2
        linarith
    have h_card_A3_A4 : #(A 3) + #(A 4) ≤ 7 := by
      rcases h_counterpart 3 with (h | h)
      . simp [h]
        specialize h_card_A2_to_A6 4
        linarith
      . simp [h]
        specialize h_card_A2_to_A6 3
        linarith
    -- Therefore, $1+8+7+7=23$ elements
    rw [h_union]
    repeat (
      apply le_trans
      repeat apply add_le_add_right
      apply card_union_le _ _
    )
    linarith
