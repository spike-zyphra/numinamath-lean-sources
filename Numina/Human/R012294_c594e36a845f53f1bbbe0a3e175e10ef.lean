import Mathlib

/- Parity of distance between natural numbers is equal to the parity of their sum. -/
lemma nat_even_dist_iff_even_add (a b : ℕ) : Even (a.dist b) ↔ Even (a + b) := by
  rw [Nat.even_add]
  rcases Nat.le_total a b with h1 | h2
  · rw [Nat.dist_eq_sub_of_le h1, Nat.even_sub h1]
    tauto
  · rw [Nat.dist_eq_sub_of_le_right h2, Nat.even_sub h2]

/- Creating a `Fin (n + 2)` using `Fin.last` and castSucc is the same as directly casting n
to `Fin (n + 2)`. -/
lemma fin_last_castsucc (n : ℕ) : (Fin.last n).castSucc = n
  := Fin.eq_of_val_eq (Nat.mod_eq_of_lt (by omega)).symm

/- Nenashev S.
Natural numbers $a_{1}, a_{2}, \ldots, a_{n}$ are such that each does not exceed its number $\left(a_{k} \leq k\right)$ and the sum of all numbers is even.
Prove that one of the sums $a_{1} \pm a_{2} \pm \ldots \pm a_{n}$ is equal to zero. -/
theorem number_theory_202733 (n : ℕ) (a : Fin n → ℕ) (hn : ∀ i, 0 < a i)
    (h₀ : ∀ i, a i ≤ i + 1) (h₁ : Even (∑ i, a i)) :
    ∃ b : Fin n → ℤ, (∀ i, b i = a i ∨ b i = -a i) ∧ ∑ i, b i = 0
  := by
    -- we prove the statement by induction on n, the number of elements
    -- we use two step induction, meaning we prove for n = 0 and n = 1 and given
    -- that n = k and n = k + 1 is true, we know that n = k + 2
    --
    -- then we'll now that it's true for every n
    induction' n using Nat.twoStepInduction with n h5 h6
    -- if the list is empty, n = 0, it's true
    · norm_num
    -- if there's only one element, n = 1, it's true
    · simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
        Fin.val_eq_zero, zero_add] at h₁ h₀
      -- 0 < a_0 ≤ 1
      have := h₀ 0
      have := hn 0
      -- so a_0 = 1
      interval_cases heq : a 0
      -- a_0 = 1, but a_0 is even, contradiction
      · norm_num at h₁
      -- let a' be the first n values of a
    · let a' : Fin n → ℕ := Fin.init <| Fin.init a
      have a'_le : ∀ (i : Fin n), a' i ≤ ↑i + 1 := fun i => h₀ _

      -- consider the case where the last two elements are equal
      rcases eq_or_ne (a n) (a (n + 1 : ℕ)) with a_eq | a_ne
      -- the sum of a values is equal to the sum of a' values plus 2 * a_n
      · have sum_eq : ∑ i : Fin (n + 2), a i = ∑ i : Fin n, a' i + 2 * a n := by
          -- bring out two last terms from sum of LHS
          simp only [Fin.sum_univ_castSucc]
          -- both last terms are equal to a_n
          rw [fin_last_castsucc, ←Fin.natCast_eq_last, ←a_eq]
          -- reorder terms on both sides
          ring_nf
          rw [add_comm]

          -- both sides are termwise equal
          congr

        -- the sum of a' is even
        have a'_sum : Even (∑ i : Fin n, a' i) := by
          simpa only [sum_eq, Nat.even_add, even_two, Even.mul_right, iff_true] using h₁

        -- every value of a' is positive
        have a'_pos : ∀ (i : Fin n), 0 < a' i := fun i => hn _

        -- apply induction hypothesis to a'
        obtain ⟨b', b1, b2⟩ := h5 a' a'_pos a'_le a'_sum

        -- then we have a valid assignment of ± for n + 2 elements
        -- it's the same assignment as for a' and the last two values have opposite sign assignments
        exists Fin.snoc (Fin.snoc b' (a n)) (-a (n + 1 : ℕ))
        constructor
        -- each sign assignment is valid
        · intro i
          -- the last value, a_(n + 1), is -a_(n + 1)
          cases' i using Fin.lastCases with h7
          · simp only [Fin.snoc_last, neg_inj, Nat.cast_inj, Fin.natCast_eq_last (n + 1), or_true]

          -- the second last value is +a_n
          cases' h7 using Fin.lastCases with h8
          · simp only [Fin.snoc_castSucc, Fin.snoc_last, Nat.cast_inj]
            rw [fin_last_castsucc]
            exact Or.inl rfl
          -- the rest are clearly valid
          simp only [Nat.cast_add, Nat.cast_one, Fin.snoc_castSucc]
          exact b1 h8
        -- the sum is zero
        -- seperate the last two values
        · simp only [Fin.sum_univ_castSucc]
          -- sum of first n elements is zero
          simp only [Nat.cast_add, Nat.cast_one, Fin.snoc_castSucc, b2, Fin.snoc_last, zero_add]
          -- (a_n) + -(a_(n + 1)) = 0, because last two terms are equal
          linarith
      -- let diff be the difference between a n and a (n + 1)
      · let diff : ℕ := Nat.dist (a n) (a (n + 1 : ℕ))

        -- diff is positive
        have diff_pos : 1 ≤ diff := by
          refine Nat.one_le_iff_ne_zero.mpr ?_
          apply Nat.eq_of_dist_eq_zero.mt
          tauto

        -- diff is at most n + 1
        have diff_le : diff ≤ n + 1 := by
          -- because both terms are at least one
          have pos1 : 1 ≤ a (n + 1 : ℕ) := hn (n + 1 : ℕ)
          have pos2 : 1 ≤ a n := hn n

          -- a_n is upper bounded by it's position plus one
          have l_1 : a n ≤ n + 1
            := by
              convert h₀ n
              norm_num
              refine (Nat.mod_eq_of_lt ?_).symm
              omega

          -- a_(n + 1) is upper bounded by it's position plus one
          have l_2 : a (n + 1 : ℕ) ≤ n + 2
            := by
              convert h₀ (n + 1 : ℕ) using 1
              simp only [Nat.cast_add, Nat.cast_one, Nat.reduceEqDiff]
              norm_cast
              refine (Nat.mod_eq_of_lt ?_).symm
              omega

          -- by considering the definition of `Nat.dist`, we see that the bound holds
          unfold diff Nat.dist
          omega

        -- let a'' be the sequence where we removed the last two elements and
        -- added an element equal to the distance between the removed elements
        let a'' : Fin (n + 1) → ℕ := Fin.snoc a' diff

        -- every value in a'' is upper bounded by it's position plus one
        have a''_le : ∀ (i : Fin (n + 1)), a'' i ≤ i + 1 := by
          intro i
          cases' i using Fin.lastCases with h7
          · simpa only [a'', Fin.snoc_last, Fin.val_last] using diff_le
          · simpa only [a'', Fin.snoc_castSucc] using a'_le h7

        -- sum of a'' is even
        have a''_even : Even (∑ i : Fin (n + 1), a'' i) := by
          -- Use that sum of a is even, and parity of a_n + a_(n + 1) is same
          -- as distance between a_n and a_(n + 1).
          simp only [a'', Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
            diff, Nat.even_add, nat_even_dist_iff_even_add, add_assoc] at h₁ ⊢
          rw [←fin_last_castsucc n, Fin.natCast_eq_last (n + 1)]
          exact h₁

        -- every value of a'' is positive
        have a''_pos : ∀ (i : Fin (n + 1)), 0 < a'' i := by
          intro i
          cases' i using Fin.lastCases with x
          · simpa only [a'', Fin.snoc_last, ne_eq] using diff_pos
          · simpa only [a'', Fin.snoc_castSucc, ne_eq] using hn <| x.castAdd 2

        -- apply induction hypothesis to a''
        obtain ⟨b, b1, b2⟩ := h6 a'' a''_pos a''_le a''_even

        -- the last value of b is either a n - a (n + 1) or a (n + 1) - a n
        have b_last_cases : b (Fin.last n) = (a n) - (a (n + 1 : ℕ))
          ∨ b (Fin.last n) = (a (n + 1 : ℕ)) - (a n) := by
          -- last value is ±|a_n - a_(n+1)|
          have last := b1 (Fin.last n)
          simp only [a'', diff, Fin.snoc_last] at last

          -- split on sign
          rcases last with pos | neg
          -- split on order of a_n and a_(n + 1)
          · rcases Nat.le_total (a n) (a (n + 1 : ℕ)) with h1 | h2
            · simpa only [Nat.dist_eq_sub_of_le h1, Nat.cast_sub h1] using Or.inr pos
            · simpa only [Nat.dist_eq_sub_of_le_right h2, Nat.cast_sub h2] using Or.inl pos
          -- split on order of a_n and a_(n + 1)
          · rcases Nat.le_total (a n) (a (n + 1 : ℕ)) with h1 | h2
            · simpa only [Nat.dist_eq_sub_of_le h1, Nat.cast_sub h1, neg_sub] using Or.inl neg
            · simpa only [Nat.dist_eq_sub_of_le_right h2, Nat.cast_sub h2, neg_sub] using Or.inr neg

        -- consider the two cases to create an "expanded" version
        rcases b_last_cases with h1 | h2
        · exists Fin.snoc (Fin.snoc (Fin.init b) (a n)) (-a (n + 1 : ℕ))
          constructor
          -- sign assignments are valid
          · intro i
            -- last case is assigned -
            cases' i using Fin.lastCases with i
            · simp only [Fin.snoc_last, or_true, Fin.natCast_eq_last (n + 1)]
            -- second to last case is assigned +
            cases' i using Fin.lastCases with i
            · simp only [← fin_last_castsucc n, Fin.snoc_castSucc, Fin.snoc_last, true_or]

            -- rest are assigned by b, which is valid
            simp only [Fin.coe_eq_castSucc, Nat.cast_add, Nat.cast_one, Fin.snoc_castSucc, Fin.init]
            convert b1 i
            all_goals
            · simp only [a', a'', Fin.coe_eq_castSucc, Fin.snoc_castSucc, Fin.init]
          -- sum with sign cases is equal to sum over b which is equal to 0
          · simp only [Fin.coe_eq_castSucc, Fin.sum_snoc, Fin.init]
            rw [Fin.sum_univ_castSucc, h1] at b2
            linarith
        · exists Fin.snoc (Fin.snoc (Fin.init b) (-(a n))) (a (n + 1 : ℕ))
          constructor
          -- sign assignments are valid
          · intro i
            -- last case is assigned +
            cases' i using Fin.lastCases with i
            · simp only [Fin.snoc_last, true_or, Fin.natCast_eq_last (n + 1)]
            -- second to last case is assigned -
            cases' i using Fin.lastCases with i
            · simp only [Fin.snoc_castSucc, Fin.snoc_last, or_true, ← fin_last_castsucc n]

            -- rest are assigned by b, which is valid
            simp only [Fin.coe_eq_castSucc, Nat.cast_add, Nat.cast_one, Fin.snoc_castSucc, Fin.init]
            convert b1 i
            all_goals
            · simp only [a', a'', Fin.coe_eq_castSucc, Fin.snoc_castSucc]
              try exact rfl
          -- sum with sign cases is equal to sum over b which is equal to 0
          · simp only [Fin.coe_eq_castSucc, Fin.sum_snoc, Fin.init]
            rw [Fin.sum_univ_castSucc, h2] at b2
            linarith