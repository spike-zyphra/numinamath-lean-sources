import Mathlib

/- Find a sequence of maximal length consisting of non-zero integers in which the sum of any seven
consecutive terms is positive and that of any eleven consecutive terms is negative.

Answer: The maximum length is 16.
One such sequence is $(-7,-7,18,-7,-7,-7,18,-7,-7,18,-7,-7,-7,18,-7,-7)$. -/
theorem combinatorics_604481 :
    IsGreatest {n | ∃ a : ℕ → ℤ, (∀ i, a i ≠ 0) ∧
      (∀ i, i + 6 < n → ∑ j ∈ Finset.range 7, a (i + j) > 0) ∧
      (∀ i, i + 10 < n → ∑ j ∈ Finset.range 11, a (i + j) < 0)} 16 := by
  constructor
  · -- We show that the maximal length is at least 16.
    -- One idea to find a suitable sequence with 16 terms is considering cycles of 7 numbers.
    -- For instance, one can try
    -- [ -a, -a, b, -a, -a, -a, b, -a, -a, b, -a, -a, -a, b, -a, -a. ]
    -- The sum of every seven consecutive numbers is (-5a + 2b) and the sum of every eleven
    -- consecutive numbers is (-8a + 3b), so (-5a + 2b > 0) and (-8a + 3b < 0), that is,
    -- [ \frac{5a}{2} < b < \frac{8a}{3} \Longleftrightarrow 15a < 6b < 16a. ]
    -- Then we can choose, say, (a = 7) and (105 < 6b < 112 \Longleftrightarrow b = 18).
    -- A valid sequence is then
    -- [ -7, -7, 18, -7, -7, -7, 18, -7, -7, 18, -7, -7, -7, 18, -7, -7. ]
    simp only [ne_eq, gt_iff_lt, Set.mem_setOf_eq]
    let a (i : ℕ) : ℤ := match i with
    | 0 => -7
    | 1 => -7
    | 2 => 18
    | 3 => -7
    | 4 => -7
    | 5 => -7
    | 6 => 18
    | 7 => -7
    | 8 => -7
    | 9 => 18
    | 10 => -7
    | 11 => -7
    | 12 => -7
    | 13 => 18
    | 14 => -7
    | 15 => -7
    | i => 1
    use a
    refine ⟨?_,?_,?_⟩
    · intro i
      aesop
    · intro i hi
      -- mechanical checking of the sums
      by_cases hc : i < 10
      · interval_cases i <;> decide
      · push_neg at hc
        linarith
    · intro i hi
      -- mechanical checking of the sums
      by_cases hc : i < 6
      · interval_cases i <;> decide
      · push_neg at hc
        linarith
  · -- We now show it is not possible to have more than 16 terms in the sequence.
    intro n hn
    -- Suppose it is possible to have more than 16 terms in the sequence.
    by_contra hc
    push_neg at hc
    -- Let (a_{1}, a_{2}, \ldots, a_{17}) be the first 17 terms of the sequence.
    simp only [ne_eq, gt_iff_lt, Set.mem_setOf_eq] at hn
    obtain ⟨a, ha, ha1, ha2⟩ := hn
    -- Consider the following array of terms in the sequence:
    -- (a_{1})(a_{2})(a_{3})(a_{4})(a_{5})(a_{6})(a_{7})(a_{8})(a_{9})(a_{10})(a_{11})
    -- (a_{2})(a_{3})(a_{4})(a_{5})(a_{6})(a_{7})(a_{8})(a_{9})(a_{10})(a_{11})(a_{12})
    -- (a_{3})(a_{4})(a_{5})(a_{6})(a_{7})(a_{8})(a_{9})(a_{10})(a_{11})(a_{12})(a_{13})
    -- (a_{4})(a_{5})(a_{6})(a_{7})(a_{8})(a_{9})(a_{10})(a_{11})(a_{12})(a_{13})(a_{14})
    -- (a_{5})(a_{6})(a_{7})(a_{8})(a_{9})(a_{10})(a_{11})(a_{12})(a_{13})(a_{14})(a_{15})
    -- (a_{6})(a_{7})(a_{8})(a_{9})(a_{10})(a_{11})(a_{12})(a_{13})(a_{14})(a_{15})(a_{16})
    -- (a_{7})(a_{8})(a_{9})(a_{10})(a_{11})(a_{12})(a_{13})(a_{14})(a_{15})(a_{16})(a_{17})

    -- Let (S) be the sum of the numbers in the array.
    let S := ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 11, a (j + k)
    -- If we sum by rows we obtain negative sums in each row, so (S < 0).
    have h : S < 0 := by
      refine Finset.sum_neg ?_ (by decide)
      intro i hi
      have : i + 10 < n := by
        linarith [List.mem_range.mp hi]
      exact ha2 i this

    -- Let S' be the sum of the numbers in the array.
    let S' := ∑ k ∈ Finset.range 11, ∑ j ∈ Finset.range 7, a (k + j)
    -- If we sum by columns we obtain positive sums in each column, so (S' > 0).
    have h' : 0 < S' := by
      refine Finset.sum_pos ?_ (by decide)
      intro i hi
      have : i + 6 < n := by
        linarith [List.mem_range.mp hi]
      exact ha1 i this

    -- However, summing by row or by column gives the same sum.
    have : S = S' := by
      exact Finset.sum_comm

    -- That one sum is negative whilst the other positive is a contradiction.
    linarith
