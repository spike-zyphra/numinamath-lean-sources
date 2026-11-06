import Mathlib
/- Let $N$ be an integer such that $N > 13$. Let $D=13$. Let $a$ and $b$ be positive integers such that $a \neq 2$ and the equation $\frac{a}{a-2} = \frac{b+N}{b+N-D}$ holds. Show that the maximum value the fraction $\frac{a}{b}$ can attain is $\frac{2k_0}{D k_640381 - N}$, where $k_640381 = \lceil \frac{N+1}{D} \rceil$. -/
theorem number_theory_640381 (n : ℕ) (hn : n > 13) : IsGreatest {S : ℚ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ a ≠ 2 ∧ (a : ℚ) / (a - 2) = (b + n) / (b + n - 13) ∧ S = (a : ℚ) / b} ((2 * ⌈(n + 1) / (13 : ℚ)⌉) / ((13 : ℚ) * ⌈(n + 1) / (13 : ℚ)⌉ - n)):= by
  constructor
  .
    -- First part: Show that the claimed maximum value is indeed in the set
    simp
    -- Define c as the ceiling of (n+1)/13
    set c:= ⌈(n + 1) / (13 : ℚ)⌉ with hc
    clear_value c
    -- Prove that c > 1
    have h1 : c > 1:= by
      have g1 : (n + 1) / (13 : ℚ) > 1:= by
        qify at hn
        linarith
      subst c
      exact Int.lt_ceil.mpr g1
    -- Use a = 2c and b = 13c - n as witnesses
    use (2 * c)
    refine ⟨by omega, ?_⟩
    use (13 * c - n)
    refine ⟨?_, ?_, ?_, ?_⟩
    .
      -- Prove that 13c - n > 0 (i.e., b > 0)
      suffices 13 * c ≥ n + 1 by omega
      qify
      suffices c ≥ (n + 1) / (13 : ℚ) by linarith
      subst c
      exact Int.le_ceil ((n + 1) / (13 : ℚ))
    .
      -- Prove that a ≠ 2
      omega
    .
      -- Prove the equation a/(a-2) = (b+n)/(b+n-13) holds
      field_simp
      set d:= c - 1 with hd
      clear_value d
      replace hd : c = d + 1:= by omega
      rw [hd]
      simp
      ring_nf
    .
      -- Prove that S = a/b equals the claimed maximum value
      field_simp
  .
    -- Second part: Show that this is indeed the greatest element
    simp [upperBounds]
    intro S a ha b hb h1 h hS
    subst S
    -- Define c as the ceiling of (n+1)/13
    set c:= ⌈(n + 1) / (13 : ℚ)⌉ with hc
    clear_value c
    -- Prove that a - 2 ≠ 0
    replace h1 : a - 2 ≠ 0:= by exact sub_ne_zero_of_ne h1
    qify at h1
    -- Prove that b + n - 13 > 0
    have h2 : b + n - (13 : ℚ) > 0:= by
      qify at hn hb
      linarith
    field_simp at h
    -- From the equation, derive that 13a = 2(b+n)
    replace hn : 13 * a = 2 * (b + n):= by
      qify
      linarith
    -- Since 13a = 2(b+n), we have 2 | 13a
    have h3 : 2 ∣ 13 * a:= by rw [hn] ; simp
    -- Since gcd(2,13) = 1, we have 2 | a
    replace h3 : 2 ∣ a:= by exact Int.dvd_of_dvd_mul_right_of_gcd_one h3 rfl
    -- Write a = 2d for some integer d
    rcases h3 with ⟨d, hd⟩
    subst a
    -- From 13a = 2(b+n), derive b = 13d - n
    replace hn : b = 13 * d - n:= by linarith
    simp
    -- Prove that d ≥ c (the ceiling value)
    have hd : d ≥ c:= by
      replace hn : 13 * d - n > 0:= by linarith
      replace hn : 13 * d ≥ n + 1:= by linarith
      qify at hn
      replace hn : d ≥ (n + 1) / (13 : ℚ):= by linarith
      subst c
      exact Int.ceil_le.mpr hn
    -- Prove that 13c - n > 0
    have hcpos : 13 * c - n > 0:= by
      suffices 13 * c ≥ n + 1 by linarith
      qify
      suffices c ≥ (n + 1) / (13 : ℚ) by linarith
      subst c
      exact Int.le_ceil ((n + 1) / (13 : ℚ))
    -- Prove that c > 0
    replace hc : c > 0:= by
      subst c
      positivity
    rw [hn]
    -- Prove that 13d - n > 0
    have hpos : 13 * d - n > 0:= by linarith
    clear hn h h1 ha h2 hb b
    simp
    qify at hcpos hpos
    -- Show that a/b ≤ the claimed maximum by cross-multiplying
    suffices 2 * (↑d : ℚ) / (13 * ↑d - ↑n) * (13 * ↑c - ↑n) ≤ 2 * ↑c by exact (le_div_iff₀ hcpos).mpr this
    rw [show 2 * ↑d / (13 * ↑d - ↑n) * (13 * ↑c - ↑n) = (2 : ℚ) * ↑d * (13 * c - n) / (13 * ↑d - ↑n) by ring]
    suffices (2 : ℚ) * ↑d * (13 * ↑c - ↑n) ≤ 2 * ↑c * (13 * ↑d - ↑n) by exact (div_le_iff₀ hpos).mpr this
    qify at hd hc
    -- The inequality reduces to (d-c)n ≥ 0, which holds since d ≥ c and n > 0
    suffices ((↑d : ℚ) - c) * n ≥ 0 by linarith
    replace hd : (↑d : ℚ) - c ≥ 0:= by linarith
    positivity
