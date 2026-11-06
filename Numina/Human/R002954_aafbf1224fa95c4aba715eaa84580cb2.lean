import Mathlib

/- Lemma 1: $n^{n+1}+1$ is not prime for $n \geq 2$. -/
lemma lemma_1 (n : ℕ) (hn : 2 ≤ n) : ¬(n ^ (n + 1) + 1).Prime := by
  -- Case analysis on parity of $n$.
  rcases Nat.even_or_odd n with h | h
  . -- Case 1: $n$ is even.
    -- Then $n + 1$ is odd, so $n + 1 \mid n^{n+1} + 1$.
    have h₁ := Odd.nat_add_dvd_pow_add_pow n 1 (show Odd (n + 1) from Even.add_one h)
    simp at h₁
    -- It suffices to show that $n + 1 < n^{n+1} + 1$.
    refine Nat.not_prime_of_dvd_of_ne h₁ (by omega) (ne_of_lt ?_)
    simp
    refine lt_self_pow₀ hn (by omega)
  . -- Case 2: $n$ is odd.
    -- Then $n + 1$ is even, so $n^{n+1} + 1$ is even.
    have h₁ : Even (n ^ (n + 1) + 1) := Odd.add_one (Odd.pow h)
    -- So we only need to show that $n^{n+1} + 1 > 2$.
    contrapose! h₁
    rw [Nat.Prime.even_iff h₁]
    refine ne_of_gt (Nat.succ_lt_succ ?_)
    exact Nat.one_lt_pow (by simp) hn

/- Lemma 2: The set of prime numbers of the form $n^{n+1}+1$ where $n$ is a positive integer is $\{2\}$. -/
lemma lemma_2 : {p | p.Prime ∧ ∃ n > 0, p = n ^ (n + 1) + 1} = {2} := by
  ext p
  simp
  constructor
  . -- Use Lemma 1, if $p$ is prime and of the form $n^{n+1}+1$ for some $n > 0$, then $n \geq 2$ is impossible.
    rintro ⟨hp, ⟨n, hn, rfl⟩⟩
    contrapose! hp
    apply lemma_1
    -- So $n$ must be $1$.
    contrapose! hp
    interval_cases n
    simp
  . -- Trivial verification.
    rintro rfl
    norm_num
    use 1
    simp

/- 4. How many prime numbers can be expressed in the form $n^{n+1}+1$, with $n$ a positive integer?
(A) 0
(B) 1
(C) 2
(D) more than 2, but finite in number
(E) infinite. -/
theorem number_theory_134979 :
    Set.encard {p | p.Prime ∧ ∃ n > 0, p = n ^ (n + 1) + 1} = 1 := by
  -- Trivial after using Lemma 2.
  rw [lemma_2]
  exact Set.encard_singleton 2
