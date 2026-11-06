import Mathlib
/- Let $S_0$ be a natural number. A sequence $(a_n)_{n \ge 0}$ is defined by its initial term $a_641242 = S_0$ and the following recurrence relations for $n > 0$:
\begin{itemize}
    \item $a_n = a_{n-1} + 2$ if $n \pmod 4 = 1$;
    \item $a_n = a_{n-1} \times 2$ if $n \pmod 4 = 2$;
    \item $a_n = a_{n-1} - 2$ if $n \pmod 4 = 3$;
    \item $a_n = a_{n-1} / 2$ if $n \pmod 4 = 0$.
\end{itemize}-
Let $V$ be a target natural number. Determine the set of natural numbers $n$ such that $a_n = V$.
Show that for $S_0=5$ and $V=80$, this set is $\{131, 136, 158, 163\}$.-/
theorem number_theory_641242 (a : ℕ → ℝ) (h1 : a 0 = 5) (hn1 : ∀ n : ℕ, a (4 * n + 1) = a (4 * n) + 2) (hn2 : ∀ n : ℕ, a (4 * n + 2) = 2 * a (4 * n + 1)) (hn3 : ∀ n : ℕ, a (4 * n + 3) = a (4 * n + 2) - 2) (hn4 : ∀ n : ℕ, a (4 * n + 4) = a (4 * n + 3) / 2) : {n : ℕ | a n = 80} = {300, 293, 134, 139}:= by

  -- Key lemma: Establish pattern for sequence values at each position mod 4
  -- For any n:
  -- a(4n) = n + 5
  -- a(4n + 1) = n + 7
  -- a(4n + 2) = 2n + 14
  -- a(4n + 3) = 2n + 12
  have h2 : ∀ n : ℕ, a (4 * n) = n + 5 ∧ a (4 * n + 1) = n + 7 ∧ a (4 * n + 2) = 2 * n + 14 ∧ a (4 * n + 3) = 2 * n + 12:= by
    intro n
    induction n with
    | zero =>
      simp
      specialize hn1 0
      specialize hn2 0
      specialize hn3 0
      specialize hn4 0
      simp at hn1 hn2 hn3 hn4
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    | succ n ih =>
      simp
      rcases ih with ⟨ih1, ih2, ih3, ih4⟩
      specialize hn1 (n + 1)
      specialize hn2 (n + 1)
      specialize hn3 (n + 1)
      specialize hn4 n
      ring_nf at ih1 ih2 ih3 ih4 hn1 hn2 hn3 hn4 ⊢
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  clear h1 hn1 hn2 hn3 hn4
  ext n
  constructor
  .
    -- Forward direction: If a_n = 80, then n must be one of {300, 293, 134, 139}
    intro h
    simp at h
    mod_cases n % 4
    .
      -- Case n ≡ 0 (mod 4)
      replace H : 4 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
      rcases H with ⟨k, hk⟩
      subst n
      replace h2:= h2 k
      rw [h2.1] at h
      replace h : k = 75:= by
        rify
        linarith
      subst k
      simp
    .
      -- Case n ≡ 1 (mod 4)
      have g1:= Nat.mod_le n 4
      rw [H] at g1
      simp at g1
      replace H : 4 ∣ n - 1:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm H))
      rcases H with ⟨k, hk⟩
      replace hk : n = 4 * k + 1:= by omega
      subst n
      specialize h2 k
      rw [h2.2.1] at h
      replace h : k = 73:= by
        rify
        linarith
      subst k
      simp
    .
      -- Case n ≡ 2 (mod 4)
      have g1:= Nat.mod_le n 4
      rw [H] at g1
      simp at g1
      replace H : 4 ∣ n - 2:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm H))
      rcases H with ⟨k, hk⟩
      replace hk : n = 4 * k + 2:= by omega
      subst n
      specialize h2 k
      rw [h2.2.2.1] at h
      replace h : k = 33:= by
        rify
        linarith
      subst k
      simp
    .
      -- Case n ≡ 3 (mod 4)
      have g1:= Nat.mod_le n 4
      rw [H] at g1
      simp at g1
      replace H : 4 ∣ n - 3:= by exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm H))
      rcases H with ⟨k, hk⟩
      replace hk : n = 4 * k + 3:= by omega
      subst n
      specialize h2 k
      rw [h2.2.2.2] at h
      replace h : k = 34:= by
        rify
        linarith
      subst k
      simp
  .
    -- Reverse direction: If n is in {300, 293, 134, 139}, then a_n = 80
    intro h
    simp at h
    simp
    rcases h with h | h | h | h
    all_goals
      subst n
    .
      specialize h2 75
      rw [h2.1]
      simp
      ring
    .
      specialize h2 73
      rw [h2.2.1]
      simp
      ring
    .
      specialize h2 33
      rw [h2.2.2.1]
      simp
      ring
    .
      specialize h2 34
      rw [h2.2.2.2]
      simp
      ring
