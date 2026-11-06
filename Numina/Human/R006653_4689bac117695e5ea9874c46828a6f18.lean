import Mathlib
set_option maxHeartbeats 400000
/- Let $A=8, B=5, C=1, D=3, E=2$. These digits form the number $85132$. It is given that these digits $A,B,C,D,E$ are distinct, and each is a natural number between 1 and 9 inclusive.
Let $N_{DE}$ be the two-digit number $10D+E$. (Thus $N_{DE}=32$).
Let $M$ be a positive integer. We are interested in integers $k$ such that $1 \le k \le M$ and $N_{DE}$ is not divisible by $k$.
Determine the count of such integers $k$.
Show that for $M=35$, this count is $M - |\{d \in \mathbb{N} \mid 1 \le d \le M \text{ and } d \text{ divides } N_{DE}\}| = 35 - 6 = 29$. -/
theorem number_theory_639693 : {d : ℕ | 1 ≤ d ∧ d ≤ 35 ∧ ¬(d ∣ 32)}.ncard = 29:= by
  -- First, explicitly list all numbers between 1 and 35 that do not divide 32
  have h1 : {d : ℕ | 1 ≤ d ∧ d ≤ 35 ∧ ¬(d ∣ 32)} = {3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35}:= by
    -- Use extensionality to prove sets are equal by showing mutual inclusion
    ext d
    constructor
    .
      -- Prove forward direction: if d is in the first set, it's in the explicit list
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3⟩
      -- Show that d is not any of the divisors of 32 (1, 2, 4, 8, 16, 32)
      replace h3 : d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 4 ∧ d ≠ 8 ∧ d ≠ 16 ∧ d ≠ 32:= by
        by_contra H
        simp at H
        -- Check each possible divisor of 32
        by_cases g1 : d = 1
        .
          subst d
          simp at h3
        .
          replace H:= H g1
          by_cases g2 : d = 2
          .
            subst d
            simp at h3
          .
            replace H:= H g2
            by_cases g3 : d = 4
            .
              subst d
              omega
            .
              replace H:= H g3
              by_cases g4 : d = 8
              .
                subst d
                omega
              .
                replace H:= H g4
                by_cases g5 : d = 16
                .
                  subst d
                  omega
                .
                  replace H:= H g5
                  subst d
                  omega
      simp
      omega
    .
      -- Prove reverse direction: if d is in the explicit list, it satisfies the conditions
      intro h
      simp at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals
        subst d
        simp
        omega
  -- Rewrite the set equality
  rw [h1]
  -- Convert from Set to Finset for counting
  rw [show ({3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35} : Set ℕ) = ({3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35} : Finset ℕ) by simp]
  -- Convert ncard to Finset.card
  rw [Set.ncard_coe_Finset]
  -- Count the elements in the Finset
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  -- Prove that all numbers in the list are distinct
  all_goals
    by_contra H
    simp at H
