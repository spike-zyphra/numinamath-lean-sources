import Mathlib
/- Theorem: Let $N$ be a three-digit natural number. Let $a$ be its hundreds digit, $b$ its tens digit, and $c$ its units digit, such that $N = 100a + 10b + c$. Assume that the units digit $c$ is not zero. Let $N_{rev}$ be the number obtained by reversing the digits of $N$, i.e., $N_{rev} = 100c + 10b + a$. If $N_{rev} - b = N$, determine the sum of all possible values of $N$. Show that the answer is 4545. -/
theorem algebra_641342 (A : Finset ℕ) (hA : A = {S : ℕ | ∃ a b c : ℕ, a > 0 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c > 0 ∧ c ≤ 9 ∧ 100 * c + 10 * b + a - b = 100 * a + 10 * b + c ∧ S = 100 * a + 10 * b + c}) : A.sum (fun x => x) = 4545:= by
  have h1 : {S : ℕ | ∃ a b c : ℕ, a > 0 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c > 0 ∧ c ≤ 9 ∧ 100 * c + 10 * b + a - b = 100 * a + 10 * b + c ∧ S = 100 * a + 10 * b + c} = {101, 202, 303, 404, 505, 606, 707, 808, 909}:= by
    -- Prove set equality by showing both directions
    ext S
    constructor
    .
      -- Forward direction: if S satisfies the condition, then S is in the explicit set
      intro h
      simp at h
      -- Extract the digits a, b, c and their constraints
      rcases h with ⟨a, ha1, ha2, b, hb, c, hc1, hc2, h1, hS⟩
      -- Simplify the equation 100*c + 10*b + a - b = 100*c + 9*b + a
      rw [show 100 * c + 10 * b + a - b = 100 * c + 9 * b + a by omega] at h1
      -- From the equation, deduce that b = 0
      have h3 : b = 0:= by omega
      subst b
      -- From the simplified equation, deduce that a = c
      have h4 : a = c:= by omega
      subst a
      -- Show that S is one of the nine possible values
      simp
      omega
    .
      -- Reverse direction: if S is in the explicit set, then S satisfies the condition
      intro h
      simp at h
      -- Case analysis on each element of the set
      rcases h with h | h | h | h | h | h | h | h | h
      all_goals
        subst S
      .
        -- Case S = 101: use a=1, b=0, c=1
        use 1, 0, 1
        simp
      .
        -- Case S = 202: use a=2, b=0, c=2
        use 2, 0, 2
        simp
      .
        -- Case S = 303: use a=3, b=0, c=3
        use 3, 0, 3
        simp
      .
        -- Case S = 404: use a=4, b=0, c=4
        use 4, 0, 4
        simp
      .
        -- Case S = 505: use a=5, b=0, c=5
        use 5, 0, 5
        simp
      .
        -- Case S = 606: use a=6, b=0, c=6
        use 6, 0, 6
        simp
      .
        -- Case S = 707: use a=7, b=0, c=7
        use 7, 0, 7
        simp
      .
        -- Case S = 808: use a=8, b=0, c=8
        use 8, 0, 8
        simp
      .
        -- Case S = 909: use a=9, b=0, c=9
        use 9, 0, 9
        simp
  -- Substitute the proven equality into the hypothesis about A
  rw [h1] at hA
  -- Convert the set equality to a finset equality
  replace hA : A = ({101, 202, 303, 404, 505, 606, 707, 808, 909} : Finset ℕ):= by
    rw [show ({101, 202, 303, 404, 505, 606, 707, 808, 909} : Set ℕ) = ({101, 202, 303, 404, 505, 606, 707, 808, 909} : Finset ℕ) by simp] at hA
    exact Finset.coe_inj.mp hA
  -- Substitute A and compute the sum
  subst A
  -- The sum 101 + 202 + 303 + 404 + 505 + 606 + 707 + 808 + 909 = 4545
  simp
