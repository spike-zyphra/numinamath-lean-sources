import Mathlib

open Finset

/-7. There is a positive integer, its $\frac{1}{2}$ is the square of an integer, its $\frac{1}{3}$ is the cube of an integer, and its $\frac{1}{5}$ is the fifth power of an integer. Then the minimum value of this number is . $\qquad$-/
theorem number_theory_263234 : IsLeast {n : ℕ | 0 < n ∧ ∃ r2 r3 r5 : ℕ, r2 ^ 2 = (1 / 2 : ℚ) * n
    ∧ r3 ^ 3 = (1 / 3 : ℚ) * n ∧ r5 ^ 5 = (1 / 5 : ℚ) * n} (2 ^ 15 * 3 ^ 10 * 5 ^ 6) := by
-- Prepare to use `padicValNat`
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
-- Split the goal to an existential subgoal and a lower bound subgoal
  simp [IsLeast, lowerBounds]; constructor
  -- Fulfill the existential goal with suitable choices of product of powers of $2$, $3$ and $5$
  · split_ands
    · use 2^7 * 3^5 * 5^3; norm_num
    · use 2^5 * 3^3 * 5^2; norm_num
    use 2^3 * 3^2 * 5; norm_num
-- To prove the lower bound goal, we first rewrite the assumptions to ℕ-type
  intro n npos r2 hr2 r3 hr3 r5 hr5
  rw [inv_mul_eq_div, eq_div_iff, mul_comm] at hr2 hr3 hr5
  norm_cast at hr2 hr3 hr5
-- Prove that $r2$, $r3$ and $r5$ are all positive
  have r2pos : 0 < r2 := by
    by_contra!; simp at this
    simp [this] at hr2; omega
  have r3pos : 0 < r3 := by
    by_contra!; simp at this
    simp [this] at hr3; omega
  have r5pos : 0 < r5 := by
    by_contra!; simp at this
    simp [this] at hr5; omega
-- Prove that $2$, $3$ and $5$ are prime factors of $n$
  have sbst : {2, 3, 5} ⊆ n.primeFactors := by
    simp [subset_iff, and_assoc]
    norm_num; split_ands
    any_goals rw [Nat.dvd_iff_mod_eq_zero]; omega
    all_goals positivity
-- Analyse the powers of $2$, $3$ and $5$ in the prime factorization of $n$
  apply_fun fun t => t.factorization at hr2 hr3 hr5
  rw [Nat.factorization_mul, Nat.factorization_pow, Finsupp.ext_iff] at hr2 hr3 hr5
  have np2_2 := hr2 2; have np3_3 := hr3 3; have np5_5 := hr5 5
  have np2_3 := hr2 3; have np3_2 := hr3 2; have np5_2 := hr5 2
  have np2_5 := hr2 5; have np3_5 := hr3 5; have np5_3 := hr5 3
  simp at np2_2 np2_3 np2_5 np3_2 np3_3 np3_5 np5_2 np5_3 np5_5
  rw [Nat.factorization_def] at np2_2 np2_3 np2_5 np3_2 np3_3 np3_5 np5_2 np5_3 np5_5
  rw [padicValNat.self] at np2_2 np3_3 np5_5
  rw [padicValNat_primes, zero_add] at np2_3 np2_5 np3_2 np3_5 np5_2 np5_3
-- Prove that the powers in the prime factorization of $n$ have the following remainders modulo $30$
  have np2 : n.factorization 2 % 30 = 15 := by omega
  have np3 : n.factorization 3 % 30 = 10 := by omega
  have np5 : n.factorization 5 % 30 = 6 := by omega
  rw [← Nat.factorization_prod_pow_eq_self (show n≠0 by positivity)]
  simp [Finsupp.prod]; rw [← union_sdiff_of_subset sbst]
-- Finish the goal by computations
  rw [prod_union]; simp; calc
    _ = 2 ^ 15 * (3 ^ 10 * 5 ^ 6) * 1 := rfl
    _ ≤ _ := by
      rw [← np2, ← np3, ← np5]
      gcongr; any_goals simp
      any_goals apply Nat.mod_le
      apply one_le_prod'; intro p hp
      simp at hp; have := hp.left.left.two_le
      apply Nat.one_le_pow; positivity
  any_goals simp
  any_goals norm_num
  all_goals positivity