import Mathlib

/- Let $n$ be a positive integer greater than $1$, and let $p$ be a prime such that
$n$ divides $p-1$ and $p$ divides $n^3-1$. Prove that $4p-3$ is a square. -/

theorem number_theory_55949 (n p : ℤ) (hp : Prime p) (hn : 1 < n) (np: 0 < p)
    (h1 : n ∣ p - 1) (h2: p ∣ n ^ 3 - 1):
    IsSquare (4 * p - 3) := by

    apply exists_eq_mul_right_of_dvd at h1
    obtain ⟨u, hu⟩ := h1

    replace hu: p = u * n + 1 := by
      linarith
    have lu: 1 ≤ u := by
      by_contra! o
      have l: 0 ≤ u := by nlinarith
      have r: u = 0 := by omega
      simp [r] at hu
      simp [hu] at hp
    rw [show n ^ 3 - 1 = (n - 1) * (n ^ 2 + n + 1) by ring] at h2
    have lp: n + 1 ≤ p := by nlinarith
    
    -- then we show that p ∣ n ^ 2 + n + 1
    replace h2: p ∣ n ^ 2 + n + 1 := by
      apply IsCoprime.dvd_of_dvd_mul_left at h2
      exact h2
      let p':= p.natAbs
      let n':= n.natAbs
      have l: p = ↑p' := by
        simp [p']
        symm
        apply abs_of_nonneg
        omega
      have r: n = ↑n' := by
        simp [n']
        symm
        apply abs_of_nonneg
        omega
      rw [l, r]
      have o: ↑n' - (1: ℤ) = ↑(n' - 1) := by
        omega
      rw [o]
      rw [Nat.isCoprime_iff_coprime]
      rw [Nat.Prime.coprime_iff_not_dvd]
      by_contra! c
      apply Nat.le_of_dvd at c
      zify at c
      rw [← o] at c
      rw [← r, ← l] at c
      linarith
      omega
      simp [p']
      rw [← Int.prime_iff_natAbs_prime]
      exact hp
    apply exists_eq_mul_right_of_dvd at h2
    obtain ⟨v, hv⟩ := h2
    have lv: 1 ≤ v := by
      by_contra! o
      have l: 0 ≤ v := by nlinarith
      have r: v = 0 := by omega
      simp [r] at hv
      nlinarith

    -- then we show that v = 1
    have ev: v = 1 := by
      by_contra! l
      replace lv: 2 ≤ v := by omega
      clear l
      rw [hu] at hv
      have s: n ^ 2 - (u * v - 1) * n - (v - 1) = 0 := by nlinarith

      -- we show that ∃ w, (u * v - 1) ^ 2 + 4 * (v - 1) = w ^ 2, which is due to sqrt formula in math
      have hw: ∃ w, 0 ≤ w ∧ (u * v - 1) ^ 2 + 4 * (v - 1) = w ^ 2 := by
        have hx: ∃ x, (u * v - 1) ^ 2 + 4 * (v - 1) = x ^ 2 := by
          set a:= u * v - 1
          set b:= v - 1
          use (2 * n - a)
          ring_nf
          nlinarith
        obtain ⟨x, hx⟩ := hx
        by_cases lx: 0 ≤ x
        .
          use x
        .
          use -x
          simp at lx
          constructor
          .
            linarith
          .
            have o: (-x) ^ 2 = x ^ 2 := by
              ring
            rw [o]
            exact hx

      obtain ⟨w, nw, hw⟩ := hw

      -- then we must have the following inequality
      have f: 2 * (u * v - 1) + 1 ≤ 4 * (v - 1) := by
        by_contra! f
        have i: (u * v - 1) ^ 2 + 4 * (v - 1) < (u * v) ^ 2 := by nlinarith
        have l1: (u * v - 1) ^ 2 < w ^ 2 := by
          rw [← hw]
          nlinarith
        rw [hw] at i
        rw [sq_lt_sq] at i l1
        have ow: |w| = w := by
          apply abs_of_nonneg
          exact nw
        rw [ow] at i l1
        rw [show |u * v - 1| = u * v - 1 by  apply abs_of_nonneg; nlinarith] at l1
        rw [show |u * v| = u * v by apply abs_of_nonneg; nlinarith] at i
        clear * - l1 i
        omega

      -- finally we use f to show contradiction
      replace f: 3 ≤ 2 * v * (2 - u) := by nlinarith
      have ou: u = 1 := by nlinarith -- hence u = 1
      simp [ou] at hv
      clear * - hv hn
      have c: n + 1 ∣ n ^ 2 + n + 1 := by
        rw [hv]
        simp
      replace c: n + 1 ∣ n := by
        nth_rewrite 2 [show n = (n + 1) ^ 2 - (n ^ 2 + n + 1) by ring]
        apply dvd_sub
        rw [show (n + 1) ^ 2 = (n + 1) * (n + 1) by ring]
        simp
        exact c
      apply exists_eq_mul_right_of_dvd at c
      obtain ⟨k, hk⟩ := c
      have o: 0 < k := by nlinarith
      replace o: 1 ≤ k := by omega
      nlinarith

    -- use v = 1, we can obtain the final result
    simp [ev] at hv
    have eq: 4 * p - 3 = (2 * n + 1) ^ 2 := by
      simp [← hv]
      ring
    rw [eq]
    apply IsSquare.sq
    
