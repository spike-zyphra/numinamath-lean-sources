import Mathlib


-- Proven by reducing to difference of squares
lemma factorization_4_2_4 (n p : ℕ) : n^4 + p^4 + (n * p)^2 =
  (n^2 + p^2 + n * p) * (n^2 + p^2 - n * p)
    := by
  calc n^4 + p^4 + (n * p)^2
  _ = (n^2 + p^2)^2 - (n * p)^2 := by
    ring_nf
    omega
  _ = (n^2 + p^2 + n * p) * (n^2 + p^2 - n * p) := by
    rw [Nat.sq_sub_sq]

theorem number_theory_611880 :
  Set.Infinite { q : ℕ | ∃ n > 0, ∃ p > 0, n ≠ p ∧
    ¬Nat.Prime (n^4 +p^4 + q^2)
  } := by

  let np_set := { q : ℕ | ∃ n > 0, ∃ p > 0, n ≠ p ∧ q = n * p }
  have np_set_inf : np_set.Infinite := by
    apply Set.Infinite.mono (s := { q | ∃ k : ℕ, q = 2 * (k + 1) })
    · intro q hq
      rcases hq with ⟨k, rfl⟩
      use 1, by linarith, 2*k + 2
      simp [mul_comm]
      linarith
    · exact Set.infinite_iff_exists_gt.mpr (fun n => ⟨2 * (n + 1), (by simp; linarith)⟩)

  let not_prime_set := { q : ℕ | ∃ n > 0, ∃ p > 0, n ≠ p ∧
    ¬Nat.Prime (n^4 +p^4 + q^2)
  }
  have ne_not_prime {q n p : ℕ} (pos_n : 0 < n) (pos_p : 0 < p) (ne : n ≠ p) : q = n * p →
      ¬Nat.Prime (n^4 + p^4 + q^2) := by
    intro eq
    subst eq
    intro h_prime
    rw [factorization_4_2_4 n p] at h_prime
    have : 0 < n ^ 2 := by
      exact Nat.sqrt_lt'.mp pos_n
    have : 0 < p ^ 2 := by
      exact Nat.sqrt_lt'.mp pos_p
    have : 0 < n * p := by
      exact Nat.mul_pos pos_n pos_p
    apply @Nat.not_prime_mul _ _ ?_ ?_ h_prime
    · intro one_eq
      omega
    · intro one_eq
      have := two_mul_le_add_sq n p
      rw [mul_assoc 2] at this
      have : 1 < n * p := by
        by_cases n = 1
        · have : 1 < p := by omega
          exact Right.one_lt_mul_of_le_of_lt pos_n this
        · have : 1 < n := by omega
          exact Left.one_lt_mul_of_lt_of_le this pos_p
      omega


  have subset_relation : np_set ⊆ not_prime_set := by
    intro q hq

    rcases hq with ⟨n, hn, p, hp, ne, rfl⟩
    use n, hn, p, hp, ne
    apply ne_not_prime _ _ _ _
    any_goals assumption
    rfl

  exact Set.Infinite.mono subset_relation np_set_inf
