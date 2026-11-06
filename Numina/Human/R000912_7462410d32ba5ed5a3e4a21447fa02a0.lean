import Mathlib

/- How many positive integers less than or equal to 10,000 are divisible by 2, 5 or 10?-/
theorem number_theory_19050 :
    Set.ncard {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ (2 ∣ n ∨ 5 ∣ n ∨ 10 ∣ n)} = 6000 := by
  have seteq : {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ (2 ∣ n ∨ 5 ∣ n ∨ 10 ∣ n)} = {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 2 ∣ n} ∪ ({n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} \ {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 10 ∣ n}) := by
    ext x
    constructor
    · -- if $x \in \{n : \mathbb{N} | n ≤ 10000 \and (2 \mid n \or 5 \mid n \or 10 \mid n)\}$ then $x \in \{n : \mathbb{N} | n ≤ 10000 \and 2 \mid n\} \union (\{n : \mathbb{N} | n ≤ 10000 \and 5 \mid n\} \backslash \{n : \mathbb{N} | n ≤ 10000 \and 10 \mid n\})$
      intro xin
      rcases xin with ⟨xne, xle, dvdx | dvdx | dvdx⟩
      left
      simp only [Set.mem_setOf_eq]
      exact ⟨xne, xle, dvdx⟩
      if dvdx2 : 2 ∣ x then
        left
        simp only [Set.mem_setOf_eq]
        exact ⟨xne, xle, dvdx2⟩
      else
        right
        simp only [Set.mem_diff, Set.mem_setOf_eq, not_and]
        constructor
        exact ⟨xne, xle, dvdx⟩
        intro _ _
        by_contra contra
        have dvdx3 : 2 ∣ x := by
          have dvd10 : 2 ∣ 10 := by
            norm_num
          exact Nat.dvd_trans dvd10 contra
        contradiction
      left
      have dvdx2 : 2 ∣ x := by
        have dvd10 : 2 ∣ 10 := by
          norm_num
        exact Nat.dvd_trans dvd10 dvdx
      simp only [Set.mem_setOf_eq]
      exact ⟨xne, xle, dvdx2⟩
    -- if $x \in \{n : \mathbb{N} | n ≤ 10000 \and 2 \mid n\} \union (\{n : \mathbb{N} | n ≤ 10000 \and 5 \mid n\} \backslash \{n : \mathbb{N} | n ≤ 10000 \and 10 \mid n\})$ then $x \in \{n : \mathbb{N} | n ≤ 10000 \and (2 \mid n \or 5 \mid n \or 10 \mid n)\}$
    intro xin
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_diff, not_and] at xin
    rcases xin with xin | xin
    constructor
    exact xin.1
    constructor
    exact xin.2.1
    left
    exact xin.2.2
    constructor
    exact xin.1.1
    constructor
    exact xin.1.2.1
    right
    left
    exact xin.1.2.2
  -- $\{n : \mathbb{N} | n ≤ 10000 \and 2 \mid n\} \cap (\{n : \mathbb{N} | n ≤ 10000 \and 5 \mid n\} \backslash \{n : \mathbb{N} | n ≤ 10000 \and 10 \mid n\}) = \empty$
  have disjoint : Disjoint {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 2 ∣ n} ({n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} \ {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 10 ∣ n}) := by
    intro s sle1 sle2
    refine le_bot_iff.mpr ?_
    rw [Set.bot_eq_empty]
    refine Set.eq_empty_of_forall_not_mem ?_
    intro x
    by_contra xins
    have xin1 : x ∈ {n | 0 < n ∧ n ≤ 10000 ∧ 2 ∣ n} := by exact sle1 xins
    have xin2 : x ∈ {n | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} \ {n | 0 < n ∧ n ≤ 10000 ∧ 10 ∣ n} := by exact sle2 xins
    have dvdx2 : 2 ∣ x := by
      exact xin1.2.2
    have dvdx5 : 5 ∣ x := by
      exact xin2.1.2.2
    have dvdx10 : 10 ∣ x := by
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by exact rfl) dvdx2 dvdx5
    simp only [Set.mem_diff, Set.mem_setOf_eq, not_and] at xin2
    have := xin2.2 xin2.1.1 xin2.1.2.1
    contradiction
  -- all the sets above are finite
  have finuniv : Finite {n : ℕ | n ≤ 10000} := by
    exact Set.finite_le_nat 10000
  have fin1 : Finite {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 2 ∣ n} := by
    have subset : {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 2 ∣ n} ⊆ {n : ℕ | n ≤ 10000} := by
      intro x xin
      exact xin.2.1
    exact Finite.Set.subset {n | n ≤ 10000} subset
  have fin2 : Finite {n | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} := by
    have subset : {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} ⊆ {n : ℕ | n ≤ 10000} := by
      intro x xin
      exact xin.2.1
    exact Finite.Set.subset {n | n ≤ 10000} subset
  have fin3 : Finite ({n | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} \ {n | 0 < n ∧ n ≤ 10000 ∧ 10 ∣ n} : Set ℕ) := by
    refine Finite.Set.finite_diff {n | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} {n | 0 < n ∧ n ≤ 10000 ∧ 10 ∣ n}
  -- $\{n : \mathbb{N} | n ≤ 10000 \and 10 \mid n\} \subset \{n : \mathbb{N} | n ≤ 10000 \and 5 \mid n\}$
  have subset : {n | 0 < n ∧ n ≤ 10000 ∧ 10 ∣ n} ⊆ {n | 0 < n ∧ n ≤ 10000 ∧ 5 ∣ n} := by
    simp only [Set.setOf_subset_setOf, and_imp]
    intro x xpos xle dvdx
    have dvdx2 : 5 ∣ x := by
      have dvd5 : 5 ∣ 10 := by
        exact Nat.dvd_of_mod_eq_zero rfl
      exact Nat.dvd_trans dvd5 dvdx
    exact ⟨xpos, xle, dvdx2⟩
  apply congrArg (fun x ↦ x.ncard) at seteq
  rw [Set.ncard_union_eq disjoint, Set.ncard_diff subset (Set.Finite.subset fin2 subset)] at seteq
  -- $\{n : \mathbb{N} | ) < n \and n ≤ a * b \and a \mid n\}$ has cardinality $b$ for any $a \neq 0$ and $b$
  have carddvdeq (a b : ℕ) : a ≠ 0 → {n | 0 < n ∧ n ≤ a * b ∧ a ∣ n}.ncard = b := by
    intro ane
    have cardeq : {n | 0 < n ∧ n ≤ a * b ∧ a ∣ n}.ncard = Nat.card {n | 0 < n ∧ n ≤ a * b ∧ a ∣ n} := by
      exact Eq.symm (Set.Nat.card_coe_set_eq {n | 0 < n ∧ n ≤ a * b ∧ a ∣ n})
    rw [cardeq]
    have cardeq2: Nat.card (Finset.Ico 0 b) = b := by
      have cardeq3 : Nat.card (Finset.Ico 0 b) = (Finset.Ico 0 b).card := by
        exact Nat.card_eq_finsetCard (Finset.Ico 0 b)
      rw [cardeq3]
      simp only [Nat.Ico_zero_eq_range, Finset.card_range]
    have card3 : Nat.card {n | 0 < n ∧ n ≤ a * b ∧ a ∣ n} = Nat.card (Finset.Ico 0 b) := by
      symm
      refine Nat.card_eq_of_bijective ?_ ?_
      -- define a function $f : [0, b] \rightarrow \{n : \mathbb{N} | n ≤ a * b \and a \mid n\}$
      intro x
      have xle := x.2
      rw [Finset.mem_Ico] at xle
      use a * (x.1 + 1)
      constructor
      simp only [add_pos_iff, zero_lt_one, or_true, mul_pos_iff_of_pos_right, gt_iff_lt]
      exact Nat.zero_lt_of_ne_zero ane
      constructor
      exact Nat.mul_le_mul_left a xle.2
      exact Nat.dvd_mul_right a (↑x + 1)
      constructor
      · -- $f$ is injective
        intro a b fab
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, mul_eq_mul_left_iff, add_left_inj, ane, or_false] at fab
        exact Subtype.eq fab
      -- $f$ is surjective
      intro n
      have npos := n.2.1
      have nle := n.2.2.1
      have dvdn := n.2.2.2
      rcases dvdn with ⟨x, hx⟩
      have xin : x - 1 ∈ Finset.Ico 0 b := by
        refine Finset.mem_Ico.mpr ?_
        constructor
        exact Nat.zero_le _
        rw [hx] at nle
        refine Nat.sub_one_lt_of_le ?_ ?_
        by_contra contra
        simp only [not_lt, nonpos_iff_eq_zero] at contra
        norm_num [hx, contra] at npos
        apply le_of_mul_le_mul_left nle (by exact Nat.zero_lt_of_ne_zero ane)
      use ⟨x - 1, xin⟩
      simp only [Set.coe_setOf, Set.mem_setOf_eq]
      have xeq : x = x - 1 + 1 := by
        refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
        by_contra contra
        simp only [not_le, Nat.lt_one_iff] at contra
        norm_num [hx, contra] at npos
      rw [xeq] at hx
      exact Subtype.eq (id (Eq.symm hx))
    rw [card3, cardeq2]
  -- so the cardinality of the original set is $5000 + (2000 - 1000) = 6000$
  have cardeq1 := carddvdeq 2 5000 (by norm_num)
  have cardeq2 := carddvdeq 5 2000 (by norm_num)
  have cardeq3 := carddvdeq 10 1000 (by norm_num)
  rw [seteq, cardeq1, cardeq2, cardeq3]
