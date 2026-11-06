import Mathlib
/- Let $a_k$ denote the last digit of the sum of the first $k$ positive integers (i.e., $a_k = (\sum_{j=1}^k j) \pmod{10}$). For any positive integer $N$, consider the sum $S_N = \sum_{k=1}^{N} a_k$. Determine the value of $S_N$. Show that $S_N$ is equal to $70 \cdot \lfloor N/20 \rfloor + \sum_{j=1}^{N \pmod{20}} a_j$, where the term $\sum_{j=1}^{N \pmod{20}} a_j$ is $0$ if $N \pmod{20} = 0$. -/
theorem number_theory_638238 (a : ℕ → ℕ) (n : ℕ) (ha : a = fun n => (∑ i in Finset.range n, (i + 1)) % 10) (hn : n > 0) : ∑ k in Finset.range n, a (k + 1) = 70 * (n / 20) + ∑ k in Finset.range (n % 20), a (k + 1):= by
  -- Prove that n is greater than or equal to n mod 20
  have h1 : n ≥ n % 20:= by exact Nat.mod_le n 20

  -- Define r as n mod 20
  set r:= n % 20 with hr
  clear_value r

  -- Prove that n is congruent to r modulo 20
  have h2 : n ≡ r [MOD 20]:= by
    subst r
    exact Nat.ModEq.symm (Nat.mod_modEq n 20)

  -- Show that 20 divides (n - r)
  replace h2 : 20 ∣ n - r:= by exact (Nat.modEq_iff_dvd' h1).mp (id (Nat.ModEq.symm h2))

  -- Extract the quotient q where n - r = 20q
  rcases h2 with ⟨q, hq⟩

  -- Express n in terms of q and r: n = 20q + r
  replace hq : n = 20 * q + r:= by omega
  clear h1

  -- Prove that r (which is n mod 20) is less than 20
  have h1 : n % 20 < 20:= by refine Nat.mod_lt n (by omega)
  rw [←hr] at h1
  clear hr

  -- Show that n divided by 20 equals q
  have h2 : n / 20 = q:= by
    subst n
    rw [show (20 * q + r) / 20 = r / 20 + q by omega]
    rw [show r / 20 = 0 by omega]
    simp

  -- Substitute and clear unnecessary hypotheses
  rw [h2]
  subst n
  clear h2 hn

  -- Prove that sum of first n natural numbers equals n(n+1)/2
  have h : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2:= by
    intro n
    suffices 2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) by omega
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith

  -- Express function a in terms of the formula n(n+1)/2 mod 10
  replace h : ∀ n : ℕ, a n  = (n * (n + 1) / 2) % 10:= by
    intro n
    simp [ha]
    rw [h n]
  clear ha

  -- Induction on q to prove the main statement
  induction q with
  | zero =>
    simp
  | succ q ih =>
    rw [show 20 * (q + 1) + r = 20 * q + r + 20 by omega]
    repeat rw [Finset.sum_range_succ]

    -- Prove that a(20q + n) = a(n) for any n
    have h2 : ∀ n : ℕ, a (20 * q + n) = a n:= by
      intro n
      simp [h]
      rw [show (20 * q + n) * (20 * q + n + 1) = 2 * (200 * q ^ 2 + 10 * q * (2 * n + 1)) + n * (n + 1) by ring_nf]
      rw [show (2 * (200 * q ^ 2 + 10 * q * (2 * n + 1)) + n * (n + 1)) / 2 = (200 * q ^ 2 + 10 * q * (2 * n + 1)) + (n * (n + 1)) / 2 by omega]
      suffices 200 * q ^ 2 + 10 * q * (2 * n + 1) + n * (n + 1) / 2 ≡ n * (n + 1) / 2 [MOD 10] by exact this
      rw [show 200 * q ^ 2 + 10 * q * (2 * n + 1) = 10 * (20 * q ^ 2 + q * (2 * n + 1)) by ring]
      set t:= 20 * q ^ 2 + q * (2 * n + 1)
      clear_value t
      have g : 10 * t ≡ 0 [MOD 10]:= by
        suffices 10 ∣ 10 * t by exact Nat.modEq_zero_iff_dvd.mpr this
        simp
      replace g : 10 * t + n * (n + 1) / 2 ≡ 0 + n * (n + 1) / 2 [MOD 10]:= by exact Nat.ModEq.add_right (n * (n + 1) / 2) g
      simp at g
      exact g

    -- Apply the periodicity property
    rw [show a (20 * q + r + 1) = a (20 * q + r + 0 + 1) by ring_nf]
    replace h2 : ∀ n : ℕ, a (20 * q + r + n + 1) = a (r + n + 1):= by
      intro n
      specialize h2 (r + n + 1)
      ring_nf at h2 ⊢
      exact h2
    repeat rw [h2 _]
    rw [h2 0, ih]

    -- Final step: prove that sum of 20 consecutive terms equals 70
    suffices a (r + 0 + 1) + a (r + 1 + 1) + a (r + 2 + 1) + a (r + 3 + 1) + a (r + 4 + 1) + a (r + 5 + 1) + a (r + 6 + 1) + a (r + 7 + 1) + a (r + 8 + 1) + a (r + 9 + 1) + a (r + 10 + 1) + a (r + 11 + 1) + a (r + 12 + 1) + a (r + 13 + 1) + a (r + 14 + 1) + a (r + 15 + 1) + a (r + 16 + 1) + a (r + 17 + 1) + a (r + 18 + 1) + a (r + 19 + 1) = 70 by linarith

    -- Prove r is in range [0,19]
    replace h1 : r ∈ Finset.range 20:= by
      simp
      exact h1
    fin_cases h1
    all_goals
      simp [h]
