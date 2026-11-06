import Mathlib

/- Déterminer tous les couples d'entiers $(n, p)$ strictement positifs où $p$ est un nombre premier et tels que $n+p$ soit une puissance de $n$.

Une puissance de $n$ est de la forme $\mathrm{n}^{\mathrm{k}}$ pour k entier naturel. -/
theorem number_theory_607285 (n p : ℕ) (hn : n > 0) (hp : Nat.Prime p)
    (hnp : ∃ k, n + p = n ^ k) :
    (n, p) = (2, 2) := by
      -- Let \((\mathfrak{p}, \mathfrak{n})\) be a potential solution pair. We have a natural number \(k\) such that \[\mathrm{n} + \mathrm{p} = \mathrm{n}^{\mathrm{k}}\]
      rcases hnp with ⟨k, hk⟩
      have hppos : p > 0 := by exact Nat.Prime.pos hp
      by_cases hkzero : k = 0
      -- First, if \(k=0\), then \(n+p=1\). However, since \(p\) is prime, \(p > 1\) and \(n \geq 0\), so \(n+p=1 < p \leq p+n\), which is absurd.
      · rw [hkzero] at hk
        simp at hk
        have : n + p > 1 := by linarith
        rw [hk] at this
        norm_num at this
      -- Therefore, \(k \geq 1\). We can then rewrite the equation as follows:\[p = n(n^{k-1} - 1)\]
      · have hkpos : k > 0 := by exact Nat.zero_lt_of_ne_zero hkzero
        -- We find that \(n\) divides \(p\).
        have hnp : n ∣ p := by
          have : n ∣ n ^ k := by exact dvd_pow_self n hkzero
          rw [← hk] at this
          exact Nat.dvd_add_self_left.mp this
        -- Since \(p\) is prime, it must be that \(n=1\) or \(n=p\). If \(n=1\), then \(1+p=1\), which is absurd since \(p \neq 0\). Thus, \(\mathrm{n} = \mathrm{p}\).
        have : n = 1 ∨ n = p := by exact (Nat.dvd_prime hp).mp hnp
        rcases this with h1 | h2
        · rw [h1] at hk
          simp at hk
          rw [hk] at hppos
          norm_num at hppos
        -- Then \(2\mathrm{p} = \mathrm{p}^{\mathrm{k}}\), so 2 divides \(p\). Thus, \(\mathrm{p} = 2\) and the equation becomes \(2+2=2^{k}\), so \(k=2\). Conversely, the pair \((2,2)\) indeed satisfies \(2+2=2^{2}\), meaning \(2+2\) is a power of 2.
        · rw [h2] at hk
          ring_nf at hk
          have hdvd : 2 ∣ p := by
            have : 2 ∣ p * 2 := by exact Nat.dvd_mul_left 2 p
            rw [hk] at this
            apply Prime.dvd_of_dvd_pow
            · apply Nat.prime_iff.mp Nat.prime_two
            · apply this
          have heven : Even p := by exact (even_iff_exists_two_nsmul p).mpr hdvd
          have := (@Nat.Prime.even_iff p hp).mp heven
          -- The only solution pair is \((2,2)\).
          rw [h2, this]
