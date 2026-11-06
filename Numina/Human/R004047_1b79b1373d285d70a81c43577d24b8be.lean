import Mathlib

/- 23. It is possible to choose, in two different ways, six different integers from 1 to 9 inclusive such that their product is a square. Let the two squares so obtained be $p^{2}$ and $q^{2}$, where $p$ and $q$ are both positive. What is the value of $p+q$ ?
A 72
B 84
C 96
D 108
E 120 -/
theorem number_theory_233368 (p q : ℕ) (hp : p > 0) (hq : q > 0)
    (h : ∃ s1 s2 : Finset ℕ, s1 ⊆ Finset.Icc 1 9 ∧ s2 ⊆ Finset.Icc 1 9 ∧
      s1 ≠ s2 ∧ s1.card = 6 ∧ s2.card = 6 ∧ (∏ i ∈ s1, i) = p^2 ∧ (∏ i ∈ s2, i) = q^2) :
    p + q = 108 := by

  have H0: ∏ i ∈ Finset.Icc 1 9, i = 362880 := by rfl

  obtain ⟨s1, s2, Hs1, Hs2, Hne, H1, H2, H3, H4⟩ := h

  -- abbreviation for the conditions that both sets has to satisfy
  set P: Finset ℕ → Prop :=
    fun s => s ⊆ Finset.Icc 1 9 ∧ s.card = 6 ∧ ∃ (w: ℕ), ∏ i ∈ s, i = w ^ 2

  -- let's prove that the number `5` can't be in any such set
  have five_not_divisor (s: Finset ℕ) (H6: P s) (H7: 5 ∈ s): False := by
    -- unfold the abbreviation `P` everywhere
    unfold P at *
    -- use information that's inside the hypothesis `H6`
    obtain ⟨H8, H9, w, H10⟩ := H6
    -- if we take the product of all numbers in the set `s`,
    -- then this product is divided by `5` (because `5 ∈ s`)
    have H11 := Finset.dvd_prod_of_mem id H7
    simp at H11
    -- the product of the elements of the set is square (from given)
    rw [H10] at H11
    -- short fact that the natural number `5` is prime number
    have H12: Nat.Prime 5 := by norm_num
    -- if `5` (which is prime) divides square of some number,
    -- it divides the number itself too
    apply Nat.Prime.dvd_of_dvd_pow H12 at H11
    -- if prime number divides some number,
    -- then it's power divides the same power of the number
    have H13: 5 ^ 2 ∣ w ^ 2 := pow_dvd_pow_of_dvd H11 2
    -- therefore `25` divides the product of all values
    -- in the big set `Finset.Icc 1 9`
    have H14: 5 ^ 2 ∣ (∏ i ∈ Finset.Icc 1 9, i) := by
      -- replace the square of `w` in the `H13`
      -- with the product of the elements of the set `s`
      rw [<- H10] at H13
      -- we prove that the product of the set `s` divides
      -- the product of the bigger set `Finset.Icc 1 9`
      have H15: (∏ i ∈ s, i) ∣ (∏ i ∈ Finset.Icc 1 9, i) :=
        Finset.prod_dvd_prod_of_subset s (Finset.Icc 1 9) (fun i => i) H8
      -- therefore, by transitive property, `25` divides
      -- the product of the set `Finset.Icc 1 9`
      exact Nat.dvd_trans H13 H15
    -- and now we have a contradiction, because the product
    -- of the set `Finset.Icc 1 9` isn't actually divided by `25`
    rw [H0] at H14
    norm_num at H14

  -- here the same principle, but with the prime number `7`.
  -- assuming that `7` is element of the set `s`,
  -- we get to the contradiction:
  -- that `49` divides the product of the set `Finset.Icc 1 9` (it doesn't)
  have seven_not_divisor (s: Finset ℕ) (H6: P s) (H7: 7 ∈ s): False := by
    unfold P at *
    obtain ⟨H8, H9, w, H10⟩ := H6
    have H11 := Finset.dvd_prod_of_mem id H7
    simp at H11
    rw [H10] at H11
    have H12: Nat.Prime 7 := by norm_num
    apply Nat.Prime.dvd_of_dvd_pow H12 at H11
    have H13: 7 ^ 2 ∣ w ^ 2 := pow_dvd_pow_of_dvd H11 2
    have H14: 7 ^ 2 ∣ (∏ i ∈ Finset.Icc 1 9, i) := by
      rw [<- H10] at H13
      have H15: (∏ i ∈ s, i) ∣ (∏ i ∈ Finset.Icc 1 9, i) :=
        Finset.prod_dvd_prod_of_subset s (Finset.Icc 1 9) (fun i => i) H8
      exact Nat.dvd_trans H13 H15
    rw [H0] at H14
    norm_num at H14

  -- we prove that for set `s` (with conditions) and
  -- for set of remaining choices (numbers)
  -- there is such number `x` that `s` is equal to
  -- the set difference of remaining numbers and sigleton set `{x}`
  have one_left_to_discard (s: Finset ℕ) (H6: P s):
      let remaining_numbers: Finset ℕ := {1, 2, 3, 4, 6, 8, 9}
      ∃ x ∈ remaining_numbers, s = remaining_numbers \ {x} := by
    -- we use the two previously proven results
    have H7 := five_not_divisor s H6
    have H8 := seven_not_divisor s H6
    -- unfold abbreviation `P` everywhere
    -- and use information from `H6`
    unfold P at *
    obtain ⟨H9, H10, w, H11⟩ := H6
    -- relatively short proof that `s` is subset of
    -- the set {1, 2, 3, 4, 5, 6, 7, 8, 9} without numbers `5` and `7`
    have H12: s ⊆ Finset.Icc 1 9 \ {5, 7} := by
      intros x Hx
      have Hx0 := H9 Hx
      simp at *
      refine ⟨Hx0, ?_, ?_⟩
      . intro Hx1; subst x; tauto
      . intro Hx1; subst x; tauto
    -- we prove an obvious fact that remaining numbers is equal to
    -- set difference `{1, 2, 3, 4, 5, 6, 7, 8, 9} \ {5, 7}`
    intro remaining_numbers
    have H13: remaining_numbers = Finset.Icc 1 9 \ {5, 7} := by
      unfold remaining_numbers
      rfl
    -- the difference of `remaining_numbers` and `s` is equal to `1`
    have H14: (remaining_numbers \ s).card = 1 := by
      rw [<- H13] at H12
      -- change `1` to difference of cardinalities of both sets
      rw [show 1 = remaining_numbers.card - s.card by rw [H10]; unfold remaining_numbers; rfl]
      -- and now we can use library lemma,
      -- because `s` is subset of remaining numbrs
      exact Finset.card_sdiff H12
    -- if cardinality of some set is `1`, then the set is singleton
    rw [Finset.card_eq_one] at H14
    -- we use this information to get some `x` that
    -- is equal to set difference of remaining_numbers and the set s
    obtain ⟨x, Hx⟩ := H14
    -- we use this `x` in the goal as a witness
    use x
    constructor
    . -- first we prove that `x` belongs to symmetric difference of
      -- remaining numbers and the set `s`
      have H14: x ∈ remaining_numbers \ s := by
        rw [Hx]
        simp
      -- now it's easy to prove that `x` is among remaining numbers
      rw [Finset.mem_sdiff] at H14
      exact H14.1
    . exact Eq.symm (sdiff_eq_symm H12 Hx)

  -- simplify the result we just proven
  -- the statement about existence of some finite set is transformed to
  -- disjunction of seven statements (for any set with fulfilled conditions)
  simp at one_left_to_discard

  -- now we prove, analysing all the `7` cases, that any set we need
  -- can be only one of two options
  have all_options (s: Finset ℕ) (H6: P s):
      s = {1, 3, 4, 6, 8, 9} ∨ s = {1, 2, 3, 4, 6, 9} := by
    -- we destruct that seven disjunction statement
    -- for the set `s` with conditions `P s` (`P` is abbreviation)
    obtain H7 | H7 | H7 | H7 | H7 | H7 | H7 := one_left_to_discard s H6 <;>
    obtain ⟨H8, H9, w, H10⟩ := H6
    . -- we reach contradiction here
      -- as the value of the product we get isn't actually perfect square
      exfalso
      rw [H7] at H10
      rw [show ∏ i ∈ {1, 2, 3, 4, 6, 8, 9} \ {1}, i = 10368 by rfl] at H10
      -- the number is perfect square iff it's square root
      -- (rounded below to the closest natural number)
      -- squared gives the original number
      have H11 := (Nat.exists_mul_self' _ ).mp ⟨w, H10.symm⟩
      -- it doesn't and `norm_num` closes the goal
      norm_num at H11
    . -- this is one of the allowed options
      left
      rw [H7]
      rfl
    . -- again contradiction.
      -- and the same in almost all following cases,
      -- except the one with another allowed set
      exfalso
      rw [H7] at H10
      rw [show ∏ i ∈ {1, 2, 3, 4, 6, 8, 9} \ {3}, i = 3456 by rfl] at H10
      have H11 := (Nat.exists_mul_self' _).mp ⟨w, H10.symm⟩
      norm_num at H11
    . exfalso
      rw [H7] at H10
      rw [show ∏ i ∈ {1, 2, 3, 4, 6, 8, 9} \ {4}, i = 2592 by rfl] at H10
      have H11 := (Nat.exists_mul_self' _).mp ⟨w, H10.symm⟩
      norm_num at H11
    . exfalso
      rw [H7] at H10
      rw [show ∏ i ∈ {1, 2, 3, 4, 6, 8, 9} \ {6}, i = 1728 by rfl] at H10
      have H11 := (Nat.exists_mul_self' _).mp ⟨w, H10.symm⟩
      norm_num at H11
    . right
      rw [H7]
      rfl
    . exfalso
      rw [H7] at H10
      rw [show ∏ i ∈ {1, 2, 3, 4, 6, 8, 9} \ {9}, i = 1152 by rfl] at H10
      have H11 := (Nat.exists_mul_self' _).mp ⟨w, H10.symm⟩
      norm_num at H11

  -- we use this theorem about two possible sets
  -- on the set `s1` and set `s2`
  have options_for_s1 := all_options s1 ⟨Hs1, H1, p, H3⟩
  have options_for_s2 := all_options s2 ⟨Hs2, H2, q, H4⟩

  -- we look at all possible (four) cases for values of sets `s1` and `s2`
  obtain H5 | H5 := options_for_s1 <;> obtain H6 | H6 := options_for_s2
  . -- here they are equal, which isn't allowed
    subst s1 s2
    tauto
  . -- use values of sets `s1` and `s2` in the statements
    -- that their products is squares of given natural numbers `p` and `q`
    rw [H5] at H3
    rw [H6] at H4
    simp at H3 H4
    -- we prove the fact about value of natural number `p`
    have Hp: p = 72 := by
      -- we apply `Nat.sqrt` to hypothesis `H3`
      -- and get that `p = 72`
      apply_fun Nat.sqrt at H3
      rw [sq, Nat.sqrt_eq] at H3
      norm_num at H3
      exact H3.symm
    -- and here the same way to prove that `q = 36`
    have Hq: q = 36 := by
      apply_fun Nat.sqrt at H4
      rw [sq, Nat.sqrt_eq] at H4
      norm_num at H4
      exact H4.symm
    subst p q
    rfl
  . -- the same idea as in the previous case
    rw [H5] at H3
    rw [H6] at H4
    simp at H3 H4
    have Hp: p = 36 := by
      apply_fun Nat.sqrt at H3
      rw [sq, Nat.sqrt_eq] at H3
      norm_num at H3
      exact H3.symm
    have Hq: q = 72 := by
      apply_fun Nat.sqrt at H4
      rw [sq, Nat.sqrt_eq] at H4
      norm_num at H4
      exact H4.symm
    subst p q
    rfl
  . -- here too they are equal, what's a contradiction with given
    subst s1 s2
    tauto