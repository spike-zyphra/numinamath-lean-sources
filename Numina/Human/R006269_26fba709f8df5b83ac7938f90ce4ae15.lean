import Mathlib
/- Let $N$ be a positive integer. Let $N_{20}$ be $N \pmod{20}$. If $N_{20} = 0$, assign $N_{20} := 20$. Determine the units digit of the sum of the first $N$ positive perfect cubes, which is $\sum_{k=1}^{N} k^3$. Show that this units digit is $V$, where $V = \left(\frac{N_{20}(N_{20}+1)}{2}\right)^2 \pmod{10}$. -/
theorem number_theory_635347 (n N : ℕ) (hn : n > 0) (hN : N = n % 20) : ∑ i in Finset.range n, (i + 1) ^ 3 ≡ (N * (N + 1) / 2) ^ 2 [MOD 10]:= by

  -- First lemma: Proves that 4 times the sum of first n cubes equals (n(n+1))²
  -- This is a key identity for the proof
  have h1 : ∀ n : ℕ, 4 * ∑ i ∈ Finset.range n, (i + 1) ^ 3 = (n * (n + 1)) ^ 2:= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      suffices (n * (n + 1)) ^ 2 + 4 * (n + 1) ^ 3 = ((n + 1) * (n + 1 + 1)) ^ 2 by linarith
      ring

  -- Apply the lemma to our specific n
  specialize h1 n
  -- Rearrange the equation to isolate the sum
  replace h1 : ∑ i ∈ Finset.range n, (i + 1) ^ 3 = (n * (n + 1)) ^ 2 / 4:= by rw [←h1] ; omega

  rw [h1]
  -- Prove that n is greater than or equal to n mod 20
  have h2 : n ≥ n % 20:= by exact Nat.mod_le n 20
  rw [←hN] at h2

  -- Prove that n and N are congruent modulo 20
  have h3 : n ≡ N [MOD 20]:= by
    rw [hN]
    exact Nat.ModEq.symm (Nat.mod_modEq n 20)

  -- Show that 20 divides n - N
  replace h3 : 20 ∣ n - N:= by exact (Nat.modEq_iff_dvd' h2).mp (id (Nat.ModEq.symm h3))
  rcases h3 with ⟨k, hk⟩

  -- Express n in terms of k and N
  replace hk : n = 20 * k + N:= by exact (Nat.sub_eq_iff_eq_add h2).mp hk

  -- Key algebraic manipulation to relate n(n+1) to N(N+1)
  have h3 : n * (n + 1) = N * (N + 1) + 20 * (k + 2 * k * N + 20 * k ^ 2):= by
    subst n
    ring_nf

  -- Define intermediate term t for cleaner expressions
  set t:= k + 2 * k * N + 20 * k ^ 2
  clear_value t

  -- Express (n(n+1))² in terms of N and t
  replace h3 : (n * (n + 1)) ^ 2 = 4 * (10 * (t * N * (N + 1) + 10 * t ^ 2)) + (N * (N + 1)) ^ 2:= by
    rw [h3]
    ring_nf

  -- Define another intermediate term s
  set s:= t * N * (N + 1) + 10 * t ^ 2
  clear_value s
  rw [h3]

  -- Simplify the division by 4
  rw [show (4 * (10 * s) + (N * (N + 1)) ^ 2) / 4 = 10 * s + (N * (N + 1)) ^ 2 / 4 by omega]

  -- Prove that (N(N+1))²/4 = (N(N+1)/2)²
  have h4 : (N * (N + 1)) ^ 2 / 4 = (N * (N + 1) / 2) ^ 2:= by
    have h4 : 2 ∣ N * (N + 1):= by
      by_cases g : Odd N
      .
        have g1 : Odd 1:= by decide
        replace g : Even (N + 1):= by exact Odd.add_odd g g1
        replace g : 2 ∣ N + 1:= by exact even_iff_two_dvd.mp g
        exact Dvd.dvd.mul_left g N
      .
        simp at g
        replace g : 2 ∣ N:= by exact even_iff_two_dvd.mp g
        exact Dvd.dvd.mul_right g (N + 1)
    rcases h4 with ⟨p, hp⟩
    rw [hp]
    norm_num
    rw [show (2 * p) ^ 2 = p ^ 2 * 4 by ring]
    omega
  rw [h4]

  -- Prove that 10s ≡ 0 (mod 10)
  have h5 : 10 * s ≡ 0 [MOD 10]:= by
    suffices 10 ∣ 10 * s by exact Nat.modEq_zero_iff_dvd.mpr this
    simp

  -- Final congruence to complete the proof
  replace h5 : 10 * s + (N * (N + 1) / 2) ^ 2 ≡ 0 + (N * (N + 1) / 2) ^ 2 [MOD 10]:= by exact Nat.ModEq.add_right ((N * (N + 1) / 2) ^ 2) h5
  simp at h5
  exact h5
