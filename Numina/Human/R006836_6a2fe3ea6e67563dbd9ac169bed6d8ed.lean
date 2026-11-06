import Mathlib
/- Let $N$ be a positive integer. A positive integer $k$ is an $\textit{abundant number}$ if the sum of its distinct proper factors is greater than $k$. (The $\textit{proper factors}$ of $k$ are all of its positive divisors except $k$ itself.) Let $C(N)$ denote the number of abundant numbers less than $N$. Show that for $N=31$, $C(N)=5$. -/
theorem number_theory_641593 : {n : ℕ | n < 31 ∧ ∑ d in Nat.properDivisors n, d > n}.ncard = 5:= by

  -- First step: prove that the set of abundant numbers less than 31 equals {12, 18, 20, 24, 30}
  have h1 : {n : ℕ | n < 31 ∧ ∑ d in Nat.properDivisors n, d > n} = {12, 18, 20, 24, 30}:= by

    -- Transform the condition using divisors instead of proper divisors
    -- Sum of divisors > 2n is equivalent to sum of proper divisors > n
    have h1 : {n : ℕ | n < 31 ∧ ∑ d in Nat.properDivisors n, d > n} = {n : ℕ | n < 31 ∧ ∑ d in Nat.divisors n, d > 2 * n}:= by
      ext n
      -- Use the relationship between sum of divisors and sum of proper divisors
      have h3 : ∑ d in Nat.divisors n, d = ∑ d in Nat.properDivisors n, d + n:= Nat.sum_divisors_eq_sum_properDivisors_add_self
      constructor
      all_goals
        intro h
        simp at h
        rcases h with ⟨h1, h2⟩
        simp
        refine ⟨h1, ?_⟩
        linarith
    rw [h1]
    clear h1
    ext n
    constructor
    .
      -- Forward direction: prove that if n < 31 and sum of proper divisors > n, then n is in {12,18,20,24,30}
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      replace h1 : n ∈ Finset.range 31:= by
        simp
        exact h1
      fin_cases h1
      all_goals
        simp
      all_goals
        norm_num at h2
      all_goals
        absurd h2
        simp
        native_decide
    .
      -- Backward direction: prove that each number in {12,18,20,24,30} satisfies the conditions
      intro h
      simp at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      all_goals
        simp
        native_decide

  -- Final step: compute the cardinality of the set {12,18,20,24,30}
  rw [h1]
  rw [show ({12, 18, 20, 24, 30} : Set ℕ) = ({12, 18, 20, 24, 30} : Finset ℕ) by simp]
  rw [Set.ncard_coe_Finset]
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  all_goals
    by_contra H
    simp at H
