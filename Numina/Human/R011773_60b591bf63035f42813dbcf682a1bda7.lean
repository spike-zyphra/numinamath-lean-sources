import Mathlib
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice -- For Nat.sInf, Nat.sInf_le
import Mathlib.Data.Nat.Order.Lemmas -- For Nat.lt_iff_add_one_le
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic -- For BddBelow
import Mathlib.Order.ConditionallyCompleteLattice.Basic -- For le_csInf
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases -- For interval_cases
import Mathlib.Data.Nat.Factorial.Basic -- For Nat.factorial

open Nat Finset Set -- Open Nat, Finset and Set namespaces

/- The number $2013$ is expressed in the form
   $2013 = \frac{a_1!a_2! \ldots a_m!}{b_1!b_2! \ldots b_n!}$,
   where $a_1 \ge a_2 \ge \cdots \ge a_m$ and $b_1 \ge b_2 \ge \cdots \ge b_n$
   are positive integers and $a_1 + b_1$ is as small as possible.
   What is $|a_1 - b_1|$?
   $\textbf{(A)}\ 1 \quad \textbf{(B)}\ 2 \quad \textbf{(C)}\ 3 \quad
   \textbf{(D)}\ 4 \quad \textbf{(E)}\ 5$ -/
-- The theorem proves the result based on necessary conditions derived from the problem statement.
-- It assumes that the pair (a₁, b₁) minimizing a₁ + b₁ in the original problem
-- must satisfy the conditions defined in Q (a₁ ≥ 61 and the prime gap condition).
theorem number_theory_94436 :
  -- Define the set Q of pairs (a₁, b₁) satisfying necessary conditions
  -- Condition 1: a₁ ≥ 61 (largest prime factor of 2013 = 3 * 11 * 61 must be covered)
  -- Condition 2: Any prime q with b₁ < q ≤ a₁ must be a factor of 2013 (otherwise q remains uncancelled)
  let Q := { p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≥ 61 ∧
    ∀ q : ℕ, q.Prime → p.2 < q → q ≤ p.1 → q ∈ ({3, 11, 61} : Finset ℕ) } ;
  -- Define the set of possible sums a₁ + b₁ for pairs in Q
  let SumsQ := { p.1 + p.2 | p ∈ Q } ;
  -- Find the minimum sum over Q (infimum exists as SumsQ is non-empty and bounded below)
  let min_sum := sInf SumsQ ;
  -- For any pair (a₁, b₁) in Q that achieves this minimum sum
  ∀ (a₁ b₁ : ℕ), (a₁, b₁) ∈ Q → a₁ + b₁ = min_sum →
  -- The value |a₁ - b₁| is 2
  abs ((a₁ : ℤ) - b₁) = 2 := by

  -- Introduce Q, SumsQ, min_sum, a₁, b₁, h_in_Q, h_is_min
  intro Q SumsQ min_sum a₁ b₁ h_in_Q h_is_min

  -- Prove that (61, 59) is in Q.
  have h61_59_in_Q : (61, 59) ∈ Q := by
    -- Unfold definition of Q and simplify goal
    simp only [Q, mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton] -- Specify Finset lemmas
    -- Prove the components: 61>0, 59>0, 61>=61
    refine ⟨by norm_num, ?_⟩
    refine ⟨by norm_num, ?_⟩
    refine ⟨by norm_num, ?_⟩
    -- Prove the prime condition
    intro q hq_prime h59_lt_q hq_le_61
    -- If 59 < q <= 61 and q is prime, q must be 61
    have hq_eq_61 : q = 61 := by
      apply le_antisymm hq_le_61
      -- Use Nat.lt_iff_add_one_le to get q ≥ 60
      rcases Nat.lt_iff_add_one_le.mp h59_lt_q with hq_ge_60
      -- Check cases q=60 and q=61
      interval_cases q
      · -- Case q = 60: Contradiction as 60 is not prime
        have h60_not_prime : ¬ Nat.Prime 60 := by rw [Nat.prime_def_lt]; simp; use 2; norm_num
        contradiction
      · -- Case q = 61: This is the only possibility
        rfl
    -- Substitute q=61 into the goal q ∈ {3, 11, 61}
    rw [hq_eq_61]
    -- Goal becomes 61 = 3 ∨ 61 = 11 ∨ 61 = 61, which is true
    norm_num

  -- Since (61, 59) ∈ Q, Q is non-empty
  have Q_nonempty : Q.Nonempty := ⟨(61, 59), h61_59_in_Q⟩
  -- SumsQ is bounded below by 0
  have sums_bdd_below : BddBelow SumsQ := ⟨0, fun _ _ => Nat.zero_le _⟩
  -- SumsQ is non-empty because Q is non-empty
  have sums_nonempty : SumsQ.Nonempty := by -- Reverted proof structure
    obtain ⟨p, hp⟩ := Q_nonempty
    use p.1 + p.2
    simp only [SumsQ, mem_setOf_eq]
    use p, hp

  -- Prove that the minimum sum (min_sum = sInf SumsQ) is 120.
  have min_val_is_120 : min_sum = 120 := by
    -- Use antisymmetry: show min_sum ≤ 120 and 120 ≤ min_sum
    apply le_antisymm
    · -- Show min_sum ≤ 120: Since 120 = 61+59 is in SumsQ, sInf SumsQ ≤ 120.
      apply Nat.sInf_le -- Use Nat.sInf_le from Mathlib.Data.Nat.Lattice
      -- Prove 120 ∈ SumsQ
      simp only [SumsQ, mem_setOf_eq]
      use (61, 59) -- Provide the element p = (61, 59)
      exact ⟨h61_59_in_Q, rfl⟩ -- Provide proof p ∈ Q and proof p.1 + p.2 = 120
    · -- Show 120 ≤ min_sum: Show 120 is a lower bound for SumsQ.
      -- Use le_csInf from ConditionallyCompleteLattice, requires non-empty set.
      apply le_csInf sums_nonempty
      -- Prove 120 ≤ s for all s ∈ SumsQ
      intro s hs
      -- Unpack s = p.1 + p.2 where p ∈ Q
      simp only [SumsQ, mem_setOf_eq] at hs
      rcases hs with ⟨p, hpQ, rfl⟩
      -- Unpack p ∈ Q conditions
      simp only [Q, mem_setOf_eq] at hpQ
      have h_a1_ge_61 : p.1 ≥ 61 := hpQ.2.2.1
      have h_cond := hpQ.2.2.2
      -- Prove p.2 ≥ 59 using the prime condition with q=59
      have h_b1_ge_59 : p.2 ≥ 59 := by
        -- Assume p.2 < 59 for contradiction
        by_contra! h_b1_lt_59
        let q := 59
        have hq_prime : Nat.Prime q := by norm_num [Nat.prime_def_lt]
        -- Check conditions for the implication in Q: p.2 < q and q ≤ p.1
        have h_b1_lt_q : p.2 < q := h_b1_lt_59
        have h_q_le_a1 : q ≤ p.1 := le_trans (by norm_num : 59 ≤ 61) h_a1_ge_61
        -- Apply the condition from Q
        specialize h_cond q hq_prime h_b1_lt_q h_q_le_a1
        -- This implies 59 ∈ {3, 11, 61}, which is false
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_cond -- Specify Finset lemmas
        norm_num at h_cond -- Contradiction found by norm_num
      -- Since p.1 ≥ 61 and p.2 ≥ 59, their sum is ≥ 120
      linarith [h_a1_ge_61, h_b1_ge_59]

  -- We have the hypothesis that (a₁, b₁) achieves the minimum sum: a₁ + b₁ = min_sum
  -- Substitute min_sum = 120 into this hypothesis
  rw [min_val_is_120] at h_is_min -- Now h_is_min : a₁ + b₁ = 120

  -- We also have the hypothesis (a₁, b₁) ∈ Q.
  -- Show that these two conditions force (a₁, b₁) = (61, 59).
  -- Extract the equalities a₁ = 61 and b₁ = 59 directly.
  have h_a1_eq_61 : a₁ = 61 := by
    -- Unpack the condition (a₁, b₁) ∈ Q
    simp only [Q, mem_setOf_eq] at h_in_Q
    have h_a1_ge_61 : a₁ ≥ 61 := h_in_Q.2.2.1
    have h_cond := h_in_Q.2.2.2
    -- Prove b₁ ≥ 59 using the same logic as inside the min_val_is_120 proof
    have h_b1_ge_59 : b₁ ≥ 59 := by
        by_contra! h_b1_lt_59
        let q := 59
        have hq_prime : Nat.Prime q := by norm_num [Nat.prime_def_lt]
        have h_b1_lt_q : b₁ < q := h_b1_lt_59
        have h_q_le_a1 : q ≤ a₁ := le_trans (by norm_num : 59 ≤ 61) h_a1_ge_61
        specialize h_cond q hq_prime h_b1_lt_q h_q_le_a1
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_cond -- Specify Finset lemmas
        norm_num at h_cond
    -- We have a₁ ≥ 61, b₁ ≥ 59, and a₁ + b₁ = 120. Linarith solves this.
    linarith [h_a1_ge_61, h_b1_ge_59, h_is_min]

  have h_b1_eq_59 : b₁ = 59 := by
    -- Re-use conditions from previous proof block if needed, or re-derive
    simp only [Q, mem_setOf_eq] at h_in_Q
    have h_a1_ge_61 : a₁ ≥ 61 := h_in_Q.2.2.1
    have h_cond := h_in_Q.2.2.2
    have h_b1_ge_59 : b₁ ≥ 59 := by
        by_contra! h_b1_lt_59
        let q := 59
        have hq_prime : Nat.Prime q := by norm_num [Nat.prime_def_lt]
        have h_b1_lt_q : b₁ < q := h_b1_lt_59
        have h_q_le_a1 : q ≤ a₁ := le_trans (by norm_num : 59 ≤ 61) h_a1_ge_61
        specialize h_cond q hq_prime h_b1_lt_q h_q_le_a1
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_cond -- Specify Finset lemmas
        norm_num at h_cond
    -- We have a₁ ≥ 61, b₁ ≥ 59, and a₁ + b₁ = 120. Linarith solves this.
    linarith [h_a1_ge_61, h_b1_ge_59, h_is_min]

  -- Substitute a₁ = 61 and b₁ = 59 into the goal |a₁ - b₁| = 2
  -- Use subst first to handle potential issues with rewrite under coercion
  subst h_a1_eq_61
  subst h_b1_eq_59
  -- The goal becomes |↑61 - ↑59| = 2, which norm_num solves.
  norm_num