import Mathlib
/- ## Task 22/88

Determine all pairs $(p ; n)$, where $p$ is a prime number and $n$ is a natural number, for which the solutions of the equation

$$
x^{2}+2\left(p^{n}+2\right) x+p^{2 n}=0
$$

are integers! -/
theorem algebra_161117 : {(p, n) : ℕ × ℕ | Nat.Prime p ∧ (∃ x1 x2 : ℤ, ∀ x : ℤ, x ^ 2 + 2 * (p ^ n + 2) * x + p ^ (2 * n) = (x - x1) * (x - x2))} = {(3, 1), (2, 3)}:= by
  ext ⟨p, n⟩
  constructor
  .
    -- Forward direction: if (p,n) satisfies the condition, then it's in our set
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    rcases h2 with ⟨x1, x2, h2⟩
    -- Test the equation with x = 1 and x = 0 to get constraints
    have h3:= h2 1
    replace h2:= h2 0
    -- From x = 0: constant term equals product of roots
    replace h2 : (-x1) * (-x2) = p ^ (2 * n):= by linarith
    -- From x = 1: coefficient of x equals negative sum of roots
    replace h3 : -x1 + -x2 = 2 * (p ^ n + 2):= by linarith
    -- Define new variables for positive roots
    set y1:= -x1
    set y2:= -x2
    clear_value y1 y2
    clear x1 x2
    -- Prime numbers are greater than 1
    have hp : p > 1:= by exact Nat.Prime.one_lt h1
    -- Prove that y1 must be positive
    have g1 : y1 > 0:= by
      by_contra H
      simp at H
      -- If y1 ≤ 0, then y2 must be negative
      have g2 : y2 < 0:= by
        by_contra H1
        simp at H1
        -- Product would be non-positive, but p^(2n) is positive
        replace H : y1 * y2 ≤ 0:= by exact Int.mul_nonpos_of_nonpos_of_nonneg H H1
        replace hp : p ^ (2 * n) > 0:= by positivity
        zify at hp
        linarith
      replace hp : p ^ n > 0:= by positivity
      zify at hp
      linarith
    -- Prove that y2 must also be positive
    have g2 : y2 > 0:= by
      by_contra H
      simp at H
      -- If y2 ≤ 0, then since y1 + y2 > 0, we have y1 > 0
      -- But then y1 * y2 ≤ 0, contradicting y1 * y2 = p^(2n) > 0
      replace g1 : y1 > 0:= by omega
      replace g1 : 0 ≤ y1:= by omega
      replace H : y1 * y2 ≤ 0:= by exact Int.mul_nonpos_of_nonneg_of_nonpos g1 H
      rw [h2] at H
      replace hp1 : p ^ (2 * n) > 0:= by positivity
      zify at hp1
      linarith
    -- Convert to natural numbers
    set x1:= y1.natAbs with hx1
    set x2:= y2.natAbs with hx2
    clear_value x1 x2
    zify at hx1 hx2
    -- Since y1 and y2 are positive, their absolute values are themselves
    rw [abs_of_pos g1] at hx1
    rw [abs_of_pos g2] at hx2
    subst y1 y2
    simp at g1 g2
    -- Now we have: x1 * x2 = p^(2n) and x1 + x2 = 2(p^n + 2)
    replace h2 : x1 * x2 = p ^ (2 * n):= by linarith
    replace h3 : x1 + x2 = 2 * (p ^ n + 2):= by linarith
    -- x1 divides p^(2n), so it must be a power of p
    have h4 : x1 ∣ p ^ (2 * n):= by
      use x2
      linarith
    replace h4 : ∃ t : ℕ, t ≤ 2 * n ∧ x1 = p ^ t:= by exact (Nat.dvd_prime_pow h1).mp h4
    rcases h4 with ⟨t, h4, h5⟩
    -- Define s = 2n - t
    set s:= 2 * n - t with hs
    clear_value s
    replace hs : s + t = 2 * n:= by omega
    subst x1
    rw [←hs] at h2
    ring_nf at h2
    -- Since x1 = p^t, we get x2 = p^s
    replace h2 : x2 = p ^ s:= by exact Nat.eq_of_mul_eq_mul_left g1 h2
    subst x2
    -- Key lemma: if p^t + p^s = 2(p^n + 2), then (p,n) is in our set
    have h : ∀ s t n : ℕ, s ≤ t → s + t = 2 * n → p ^ t + p ^ s = 2 * (p ^ n + 2) → (p, n) ∈ ({(3, 1), (2, 3)} : Set (ℕ × ℕ)):= by
      intro s t n g hs h3
      -- Prove that p^s divides 4
      have g3 : p ^ s ∣ 4:= by
        ring_nf at h3
        have g3 : p ^ s ∣ p ^ n * 2:= by
          use p ^ (n - s) * 2
          rw [show p ^ s * (p ^ (n - s) * 2) = p ^ (s + (n - s)) * 2 by ring]
          rw [show s + (n - s) = n by omega]
        suffices p ^ s ∣ p ^ t + p ^ s by rw [h3] at this ; exact (Nat.dvd_add_iff_left g3).mpr this
        use p ^ (t - s) + 1
        rw [show p ^ s * (p ^ (t - s) + 1) = p ^ s + p ^ (s + (t - s)) by ring]
        rw [show s + (t - s) = t by omega]
        ring
      -- Case analysis on s
      by_cases g4 : s = 0
      .
        -- Case s = 0
        subst s
        simp at hs
        subst t
        simp at h3
        -- This leads to p^(2n) = 2p^n + 3
        replace h3 : p ^ (2 * n) = 2 * p ^ n + 3:= by linarith
        replace hp : p ^ n > 0:= by positivity
        set z:= p ^ n - 1 with hz
        clear_value z
        replace hz : p ^ n = z + 1:= by omega
        rw [show p ^ (2 * n) = (p ^ n) ^ 2 by ring] at h3
        rw [hz] at h3
        -- This gives z^2 = 4, so z = 2
        replace h3 : z ^ 2 = 4:= by linarith
        replace h3 : z = 2:= by nlinarith only [h3]
        subst z
        simp at hz
        have g4 : Nat.Prime 3:= by norm_num
        -- This forces p = 3 and n = 1
        replace hz : p = 3 ∧ n = 1:= by exact (Nat.Prime.pow_eq_iff g4).mp hz
        rcases hz with ⟨rfl, rfl⟩
        simp
      .
        -- Case s > 0
        have g5 : p = 2:= by
          have g5 : p ∣ 2 ^ 2:= by
            simp
            suffices p ∣ p ^ s by exact Nat.dvd_trans this g3
            use p ^ (s - 1)
            rw [show p * p ^ (s - 1) = p ^ (1 + (s - 1)) by ring]
            rw [show 1 + (s - 1) = s by omega]
          replace g5 : p ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow h1 g5
          have g6 : Nat.Prime 2:= by norm_num
          exact (Nat.prime_dvd_prime_iff_eq h1 g6).mp g5
        subst p
        -- Since p = 2 and 2^s divides 4, we have s ≤ 2
        replace g3 : s ≤ 2:= by
          rw [show 4 = 2 ^ 2 by ring] at g3
          exact (Nat.pow_dvd_pow_iff_le_right hp).mp g3
        replace g3 : s = 1 ∨ s = 2:= by omega
        rcases g3 with rfl | rfl
        .
          -- Case s = 1
          simp at h3
          replace h3 : 2 ^ (2 * n) = 4 * 2 ^ n + 4:= by
            rw [←hs]
            ring_nf
            linarith
          zify at h3
          -- This would require 8 to be a perfect square, which is false
          replace h3 : IsSquare (8 : ℤ):= by
            use 2 ^ n - 2
            ring_nf at h3 ⊢
            linarith
          absurd h3
          native_decide
        .
          -- Case s = 2
          simp at h3
          replace h3 : 2 ^ t = 2 ^ (n + 1):= by
            ring_nf
            linarith
          replace h3 : Nat.log 2 (2 ^ t) = Nat.log 2 (2 ^ (n + 1)):= by rw [h3]
          rw [Nat.log_pow (by omega) _] at h3
          rw [Nat.log_pow (by omega) _] at h3
          subst t
          -- This forces n = 3
          replace hs : n = 3:= by omega
          subst n
          simp
    -- Apply the lemma, handling both cases s ≤ t and t ≤ s
    by_cases g : s ≤ t
    .
      exact h s t n g hs h3
    .
      exact h t s n (by omega) (by linarith) (by linarith)
  .
    -- Reverse direction: verify that (3,1) and (2,3) satisfy the condition
    intro h
    simp at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp
      norm_num
    .
      -- For (3,1): use roots -1 and -9
      use -1, -9
      intro x
      ring_nf
    .
      -- For (2,3): use roots -4 and -16
      use -4, -16
      intro x
      ring_nf
