import Mathlib

/- If two non-empty sets are subsets of a common set, and the sum of the cardinalities of the smaller
  sets are larger than the common set, then the sets are not disjoint. -/
lemma Finset_not_disjoint_of_card_lt {A : Type*} [DecidableEq A] (s t u: Finset A) (h1 : u.card < s.card + t.card) (h2 : s ⊆ u) (h3 : t ⊆ u)
: ¬Disjoint s t := by

  -- note that the union of s and t are also subsets of u
  have un_subs : s ∪ t ⊆ u := Finset.union_subset h2 h3

  -- so the cardinality of the union is at most the cardinality of u
  have card_le : (s ∪ t).card ≤ u.card := Finset.card_le_card un_subs

  -- but assume s and t are not disjoint
  by_contra d

  -- then the cardinality of the union is the cardinality of s plus the cardinality of t
  have union_card : (s ∪ t).card = s.card + t.card := Finset.card_union_of_disjoint d

  -- but that goes against our assumption, so s and t are disjoint
  linarith


/- 5.100 In a certain election campaign, various parties made a total of $p$ different promises $(p > 0)$, some parties can make the same promises, any two parties have at least one common promise, but no two parties made exactly the same set of promises. Prove that the number of parties is no more than $2^{p-1}$.

将上面的文本翻译成英文，请保留源文本的换行和格式，直接输出翻译结果。 -/
theorem algebra_214020 {n : ℕ} (p : ℕ) (hp : 0 < p)
    (a : Fin n → Finset (Fin p)) (ha : ∀ i j, i ≠ j → ¬Disjoint (a i) (a j))
    (h' : Function.Injective a) :
    n ≤ 2 ^ (p - 1) := by
      -- The sets of policies are non-trivial
      have : Nontrivial (Finset (Fin p)) := by
        refine @Finset.instNontrivial ?_ ?_
        exact Fin.pos_iff_nonempty.mp hp

      -- For every i and j, there is no party i and j which has policies which are eachothers complement.
      have no_compl : ∀ i j, (a i)ᶜ ≠ (a j) := by
        intro i j
        -- first consider when i = j
        by_cases eq : i = j
        -- a set of policies can't be the complement of itself
        · exact eq ▸ compl_ne_self
        -- we have that i and j policies are not disjoint
        · have not_disjoint := ha i j eq
          -- but let's assume they are complement of eachother
          by_contra hmm

          -- but then i policies and it's complement are not disjoint
          rw [←hmm] at not_disjoint

          -- this is absurd
          exact absurd disjoint_compl_right not_disjoint

      -- consider the set of sets of policies which the parties have
      let all_sets := Finset.univ.map ⟨a, h'⟩

      -- we have n parties, so there are n sets of policies
      have all_sets_card : all_sets.card = n := by
        norm_num [all_sets]

      -- take the complement of each set of polcicies
      let all_sets_compl := all_sets.map ⟨compl, compl_injective⟩

      -- we have n complements of policies
      have all_sets_compl_card : all_sets_compl.card = n := by
        norm_num [all_sets_compl, all_sets_card]

      -- the total number of possible sets of policies is 2 ^ p
      have univ_card : (Finset.univ : Finset (Finset (Fin p))).card = 2 ^ p
        := by norm_num

      -- so let's assume that n ≤ 2 ^ (p - 1) is not true
      by_contra ltt

      -- then we have that 2 ^ (p - 1) < n
      replace ltt : 2 ^ (p - 1) < n := by linarith

      -- but then the sets of policies and their complements are not disjoint
      have not_disjoint : ¬Disjoint all_sets all_sets_compl := by
        apply Finset_not_disjoint_of_card_lt all_sets all_sets_compl Finset.univ
        -- because the cardinality of sets of policies plus cardinality
        -- of complements of sets of policies is larger than the total set of possible sets of policies
        · rw [univ_card, all_sets_card, all_sets_compl_card]
          convert_to 2 ^ (p - 1) + 2 ^ (p - 1) < n + n
          · field_simp
          linarith
        · exact Finset.subset_univ all_sets
        · exact Finset.subset_univ all_sets_compl

      -- so let x be a set of policies which is a real set of policies and one of the complements
      obtain ⟨x, xh⟩ := Finset.not_disjoint_iff.mp not_disjoint

      -- then some party i has x as policies, and some party j has the complement of x as policies
      norm_num [all_sets, all_sets_compl] at xh
      obtain ⟨⟨i, ih⟩, ⟨j, jh⟩⟩ := xh

      -- so the complement of j policies is equal to i policies
      have compl_eq : (a j)ᶜ = a i := ih ▸ jh

      -- but we already showed that no party has the complement of another parties policies
      have compl_ne : (a j)ᶜ ≠ a i := no_compl j i

      -- this is a contradiction
      contradiction