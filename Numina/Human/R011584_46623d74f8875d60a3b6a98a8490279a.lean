import Mathlib

/- When setting up a code lock, each of the 26 Latin letters on its keyboard is assigned a natural number known only to the owner of the lock. Different letters may be assigned the same number. After entering any combination of pairwise distinct letters, the numerical values corresponding to the entered letters are summed. The lock opens if the sum is divisible by 26. Prove that for any numerical values assigned to the letters, there exists a combination that opens the lock.

# -/
theorem number_theory_205479 (a : Fin 26 → ℕ) :
    ∃ b : Finset (Fin 26), b.card > 0 ∧ 26 ∣ ∑ i ∈ b, a i := by

  -- rewrite goal to change the part about divisibility of the sum by `26`
  -- to equality of the sum (mod 26) to `0: Fin 26`
  simp_rw [<- Fin.natCast_eq_zero, Nat.cast_sum]

  -- define helper function `f`, that takes `n: Fin 26` (number less than 26) and
  -- calculates the sum (mod 26) over all values from 0 to n
  set f: Fin 26 → Fin 26 := fun (n: Fin 26) => ∑ i ∈ Finset.Icc 0 n, (a i: Fin 26)

  -- there are two cases:
  -- 1) there's some `n: Fin 26`, such that the sum on `Finset.Icc 0 n` is zero
  -- 2) there's no such `n: Fin 26`, such that the sum on `Finset.Icc 0 n` is zero
  obtain some_sum_eq_zero | all_sums_ne_zero :=
    em (∃ (n: Fin 26), f n = 0)

  . -- first case is simple to solve
    -- get the `n: Fin 26` from `some_sum_eq_zero` and use `Finset.Icc 0 n` in the goal
    obtain ⟨n, sum_Icc_0_n_eq_zero⟩ := some_sum_eq_zero
    use (Finset.Icc 0 n)
    constructor
    . simp
    . exact sum_Icc_0_n_eq_zero

  . -- second case, when there is no such nice `n: Fin 26`

    -- let's prove very useful lemma:
    -- if there are two values `k n: Fin 26` where `k` is less than `n` and
    -- if `f k` = `f n`, then we have the necessary `Finset (Fin 26)` to solve the goal
    have main_result (k n: Fin 26) (Hkn: k < n) (Hsums: f k = f n):
        ∃ b, b.card > 0 ∧ ∑ x ∈ b, (a x: Fin 26) = 0 := by
      -- we use finset of all values from `k + 1` to `n`
      use (Finset.Icc (k + 1) n)
      constructor
      . -- easy to prove
        simp; omega
      . -- we express this finset as difference of two other finsets
        have aux: Finset.Icc (k + 1) n = Finset.Icc 0 n \ Finset.Icc 0 k := by
          ext x; simp; omega
        -- and also we will use this lemma about one finset being subset of another
        have aux0: Finset.Icc 0 k ⊆ Finset.Icc 0 n := by
          intro x; simp; omega
        -- unfold the meaning of `f` in hypothesis `Hsums`
        simp [f] at Hsums
        -- here we change the finset in the goal to difference of two subsets
        -- then we use the theorem `Finset.sum_sdiff_eq_sub` which states:
        -- if finset `t`is subset of finset `s`, then
        -- sum over difference `s \ t` is equal to
        -- difference of sum over `s` and sum over `t`
        -- (in out case both sums are equal, therefore the difference is 0)
        rw [aux, Finset.sum_sdiff_eq_sub aux0, Hsums, sub_self]

    -- define finset over all values of type `Fin 26`
    -- and also finset that contains all nonzero values of `Fin 26`
    set all_fins: Finset (Fin 26) := Finset.univ
    set nonzero_fins: Finset (Fin 26) := all_fins \ {0}

    -- cardinality of finset `all_fins` is 26
    have all_fins_card: all_fins.card = 26 := by simp [all_fins]
    -- cardinality of finset `nonzero_fins` is 25, because value 0 is taken away
    have nonzero_fins_card: nonzero_fins.card = 25 := by
      simp only [nonzero_fins, all_fins]
      rw [Finset.card_univ_diff]
      simp

    -- the first lemma to use in the variation of pigeonhole principle
    -- (the number of nonzero `Fin 26` values is
    -- less than total number of `Fin 26` values)
    have pigeonhole_aux_1: nonzero_fins.card < all_fins.card := by
      simp [all_fins_card, nonzero_fins_card]

    -- the second lemma for pigeonhole principle theorem
    -- (the function `f` puts all values into finset of nonzero valus)
    have pigeonhole_aux_2 (x: Fin 26) (Hx: x ∈ all_fins):
        f x ∈ nonzero_fins := by
      simp_all [f, all_fins, nonzero_fins]

    -- now we finally use pigeonhole principle
    have pigeonhole_principle :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to pigeonhole_aux_1 pigeonhole_aux_2

    -- we get two different values `n1`, `n2`, such that
    -- `f n1` and `f n2` are equal (nonzero) values
    obtain ⟨n1, H1, n2, H2, Hne, Hsum_eq⟩ := pigeonhole_principle

    -- we have read the end: either `n1 < n2` or `n2 < n1`,
    -- and in each case we simply use the lemma `main_result`
    have two_cases: n1 < n2 ∨ n2 < n1 := lt_or_gt_of_ne Hne
    obtain H | H := two_cases
    . exact (main_result n1 n2 H Hsum_eq)
    . exact (main_result n2 n1 H Hsum_eq.symm)