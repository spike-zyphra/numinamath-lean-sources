import Mathlib
/- Let $p$ be an odd prime number. Let $s_0$ be an integer such that $0 < s_638433 < p/2$. Let $a$ be the integer $s_0^2 \pmod p$.
Show that for an integer $x$ satisfying $0 \le x < p$, the congruence $x^2 \equiv a \pmod p$ holds if and only if $x = s_0$ or $x = p - s_0$. -/
theorem number_theory_638433 (s x p : ℕ) (hp : Nat.Prime p) (hs1 : 0 < s) (hs2 : (s : ℚ) < p / 2) (hx1 : 0 < x) (hx2 : x < p) : x ^ 2 ≡ s ^ 2 [MOD p] ↔ x = s ∨ x = p - s:= by
  -- We prove both directions of the equivalence
  constructor
  .
    -- Forward direction: if x² ≡ s² (mod p), then x = s or x = p - s
    intro h
    -- Case analysis on whether x ≥ s
    by_cases h1 : x ≥ s
    .
      -- Case 1: x ≥ s
      -- First show that x² ≥ s²
      have h2 : x ^ 2 ≥ s ^ 2:= by exact Nat.pow_le_pow_of_le_left h1 2
      -- Convert congruence to divisibility
      replace h : p ∣ x ^ 2 - s ^ 2:= by exact (Nat.modEq_iff_dvd' h2).mp (id (Nat.ModEq.symm h))
      -- Let y = x - s
      set y:= x - s with hy
      clear_value y
      -- Consider the case y = 0
      by_cases hy1 : y = 0
      .
        -- If y = 0, then x = s
        subst y
        replace hy : x = s:= by omega
        left
        exact hy
      .
        -- If y ≠ 0, use factorization (x + s)(x - s)
        replace hy2 : x = y + s:= by omega
        subst x
        -- Algebraic manipulation to get y(y + 2s)
        have g1 : (y + s) ^ 2 - s ^ 2 = y * (y + 2 * s):= by
          suffices (y + s) ^ 2 = s ^ 2 + y * (y + 2 * s) by omega
          ring
        rw [g1] at h
        -- Use prime property to split the divisibility
        replace h : p ∣ y ∨ p ∣ y + 2 * s:= by exact (Nat.Prime.dvd_mul hp).mp h
        rcases h with h | h
        .
          -- Show that y = p leads to contradiction
          replace h:= Nat.le_of_dvd (by omega) h
          replace h : y = p:= by omega
          clear hy
          omega
        .
          -- Show that y + 2s = p, leading to x = p - s
          rcases h with ⟨c, hc⟩
          -- Prove c = 1 using bounds
          have hc1 : c ≥ 1:= by
            by_contra H
            simp at H
            subst c
            simp at hc
            replace hc:= hc.1
            trivial
          have hc2 : c < 2:= by
            by_contra H
            simp at H
            replace H : p * 2 ≤ p * c:= by exact Nat.mul_le_mul_left p H
            linarith
          replace hc1 : c = 1:= by omega
          subst c
          simp at hc
          right
          omega
    .
      -- Case 2: x < s
      -- Similar to Case 1 but with roles of x and s reversed
      simp at h1
      have h2 : x ^ 2 < s ^ 2:= by refine Nat.pow_lt_pow_left h1 (by omega)
      replace h : p ∣ s ^ 2 - x ^ 2:= by
        replace h2 : x ^ 2 ≤ s ^ 2:= by omega
        exact (Nat.modEq_iff_dvd' h2).mp h
      set y:= s - x with hy
      clear_value y
      replace hy : s = y + x:= by omega
      subst s
      simp at h1
      have h3 : (y + x) ^ 2 - x ^ 2 = y * (y + 2 * x):= by
        have g1 : (y + x) ^ 2 = x ^ 2 + y * (y + 2 * x):= by
          suffices (y + x) ^ 2 = x ^ 2 + y * (y + 2 * x) by omega
          ring
        omega
      rw [h3] at h
      replace h : p ∣ y ∨ p ∣ y + 2 * x:= by exact (Nat.Prime.dvd_mul hp).mp h
      rcases h with h | h
      .
        -- Show that y = p leads to contradiction with s < p/2
        replace h:= Nat.le_of_dvd (by omega) h
        qify at h
        simp at hs2
        linarith
      .
        -- Show that y + 2x = p, leading to x = p - s
        rcases h with ⟨c, hc⟩
        have hc1 : c ≥ 1:= by
          by_contra H
          simp at H
          subst c
          simp at hc
          replace hc:= hc.1
          omega
        have hc2 : c < 2:= by
          by_contra H
          simp at H
          replace H : p * 2 ≤ p * c:= by exact Nat.mul_le_mul_left p H
          simp at hs2
          rw [←hc] at H
          qify at H
          linarith
        replace hc1 : c = 1:= by omega
        subst c
        simp at hc
        right
        omega
  .
    -- Backward direction: if x = s or x = p - s, then x² ≡ s² (mod p)
    intro h
    rcases h with h | h
    .
      -- Case: x = s is trivial
      subst x
      rfl
    .
      -- Case: x = p - s
      -- Again split into cases x ≥ s and x < s
      by_cases h1 : x ≥ s
      .
        -- Case x ≥ s: use factorization (x + s)(x - s)
        have h2 : x ^ 2 ≥ s ^ 2:= by exact Nat.pow_le_pow_of_le_left h1 2
        suffices p ∣ x ^ 2 - s ^ 2 by exact Nat.ModEq.symm ((fun {n a b} h => (Nat.modEq_iff_dvd' h).mpr) h2 this)
        set y:= x - s with hy
        clear_value y
        replace hy : x = y + s:= by omega
        rw [hy]
        have h3 : (y + s) ^ 2 - s ^ 2 = y * (y + 2 * s):= by
          have g1 : (y + s) ^ 2 = s ^ 2 + y * (y + 2 * s):= by
            suffices (y + s) ^ 2 = s ^ 2 + y * (y + 2 * s) by omega
            ring
          omega
        rw [h3]
        subst x
        replace hy : p = y + 2 * s:= by omega
        subst p
        simp
      .
        -- Case x < s: similar to above
        replace h1 : x ≤ s:= by omega
        replace h2 : x ^ 2 ≤ s ^ 2:= by exact Nat.pow_le_pow_of_le_left h1 2
        suffices p ∣ s ^ 2 - x ^ 2 by exact (Nat.modEq_iff_dvd' h2).mpr this
        set y:= s - x with hy
        clear_value y
        replace hy : s = y + x:= by omega
        rw [hy]
        have h3 : (y + x) ^ 2 - x ^ 2 = y * (y + 2 * x):= by
          have g1 : (y + x) ^ 2 = x ^ 2 + y * (y + 2 * x):= by
            suffices (y + x) ^ 2 = x ^ 2 + y * (y + 2 * x) by omega
            ring
          omega
        rw [h3]
        subst s
        replace h : p = y + 2 * x:= by omega
        subst p
        simp
