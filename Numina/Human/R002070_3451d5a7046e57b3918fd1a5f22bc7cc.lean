import Mathlib

/- Suppose that we have a set $S$ of $756$ arbitrary integers between $1$ and $2008$ ($1$ and $2008$ included).
Prove that there are two distinct integers $a$ and $b$ in $S$ such that their sum $a + b$ is divisible by $8$. -/
theorem number_theory_61488 (S : Finset ℕ) (h1 : S.card = 756)
    (h2 : S ⊆ Finset.Icc 1 2008) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ 8 ∣ a + b := by
  -- S can be devided into 8 sets by modulo 8
  let S0 := S.filter (· % 8 = 0)
  let S1 := S.filter (· % 8 = 1)
  let S2 := S.filter (· % 8 = 2)
  let S3 := S.filter (· % 8 = 3)
  let S4 := S.filter (· % 8 = 4)
  let S5 := S.filter (· % 8 = 5)
  let S6 := S.filter (· % 8 = 6)
  let S7 := S.filter (· % 8 = 7)

  -- ... that are no more than 251 numbers each
  have h_card : ∀ n < 8, (S.filter (· % 8 = n)).card ≤ 251 := by
    intros n h
    have := Finset.filter_subset_filter (· % 8 = n) h2
    have := Finset.card_le_card this
    interval_cases hn : n
    all_goals
    have : ((Finset.Icc 1 2008).filter (· % 8 = n)).card = 251 := by
      subst n
      native_decide
    subst n
    omega

  -- and their union is S.
  have h_union : S = S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 := by
    apply Finset.ext
    intro a
    constructor
    . intro h
      let r := a % 8
      have : r < 8 := by omega
      simp [S0, S1, S2, S3, S4, S5, S6, S7]
      interval_cases h1 : r <;> tauto
    . simp [S0, S1, S2, S3, S4, S5, S6, S7]
      rintro (h|h|h|h|h|h|h|h) <;> tauto

  -- We prove by contradiction.
  by_contra! h

  have h_card_S0 : S0.card ≤ 1 := ?h0
  have h_card_S4 : S4.card ≤ 1 := ?h4
  case h0 | h4 =>
    -- If there are more than 2 numbers in S0 or S4, they'd have a sum divided by 8, hence a contradiction.
    by_contra! h1
    obtain ⟨t, h1, h2⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt h1)
    rw [Finset.card_eq_two] at h2
    obtain ⟨x, y, hne, h2⟩ := h2
    simp [h2, S0, S4, Subset] at h1
    specialize h x (by tauto) y (by tauto) hne
    omega

  -- If both of, say S1 and S7, have numbers, take one number from each of them and the sum will be divided by 8.
  -- Thus one of them must be empty, so their number count in total can't exceed 251.
  have h_card_general : ∀ n ∈ Finset.Icc 1 3,
      (S.filter (· % 8 = n)).card + (S.filter (· % 8 = 8 - n)).card ≤ 251 := by
    intro n hn
    simp at hn
    by_cases h1 : S.filter (· % 8 = n) = ∅
    . simp [h1]
      apply h_card
      omega
    by_cases h2 : S.filter (· % 8 = 8 - n) = ∅
    . simp [h2]
      apply h_card
      omega
    rw [←ne_eq, ←Finset.nonempty_iff_ne_empty] at h1 h2
    obtain ⟨x, hx⟩ := h1
    obtain ⟨y, hy⟩ := h2
    simp at hx hy
    specialize h x (by tauto) y (by tauto) (by omega)
    omega

  -- This is the case for S1 and S7
  have h_card_S1_S7 : S1.card + S7.card ≤ 251 := by
    simp [S1, S7]
    apply h_card_general
    simp

  -- S2 and S6
  have h_card_S2_S6 : S2.card + S6.card ≤ 251 := by
    simp [S2, S6]
    apply h_card_general
    simp

  -- S3 and S5
  have h_card_S3_S5 : S3.card + S5.card ≤ 251 := by
    simp [S3, S5]
    apply h_card_general
    simp

  -- Sum all this up, S can't have more than 755 numbers, which is a contradiction.
  have h_card_S_le : S.card ≤ 755 := by
    rw [h_union]
    calc (S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7).card
      _ ≤ (S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6).card + S7.card := ?le1
      _ ≤ (S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5).card + S6.card + S7.card := ?le2
      _ ≤ (S0 ∪ S1 ∪ S2 ∪ S3 ∪ S4).card + S5.card + S6.card + S7.card := ?le3
      _ ≤ (S0 ∪ S1 ∪ S2 ∪ S3).card + S4.card + S5.card + S6.card + S7.card := ?le4
      _ ≤ (S0 ∪ S1 ∪ S2).card + S3.card + S4.card + S5.card + S6.card + S7.card := ?le5
      _ ≤ (S0 ∪ S1).card + S2.card + S3.card + S4.card + S5.card + S6.card + S7.card := ?le6
      _ ≤ S0.card + S1.card + S2.card + S3.card + S4.card + S5.card + S6.card + S7.card := ?le7
      _ ≤ 755 := by omega
    all_goals
    repeat apply add_le_add_right
    apply Finset.card_union_le
  omega
