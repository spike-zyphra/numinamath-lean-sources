import Mathlib
/- Let $M$ be a positive integer. Show that there exists an irrational number $\alpha > 1$ such that for all positive integers $n$, the floor of $\alpha^n$ is congruent to $0 \pmod M$. -/
theorem algebra_634839 (m : ℕ) (h1 : m ≥ 2) : ∃ (r : ℝ), (Irrational r) ∧ (r > 1) ∧ (∀ (n : ℕ), n ≥ 1 → ⌊(r ^ n)⌋ ≡ 0 [ZMOD m]):= by
  -- Define s as the smaller root of the quadratic equation x^2 - (2m+1)x + m = 0
  set s:= (2 * m + 1 - √(4 * m ^ 2 + 1)) / 2 with hs
  -- Define r as the larger root of the quadratic equation x^2 - (2m+1)x + m = 0
  set r:= (2 * m + 1 + √(4 * m ^ 2 + 1)) / 2 with hr
  -- Clear the values to work with the definitions
  clear_value s r
  -- Prove that both s and r satisfy the quadratic equation x^2 - (2m+1)x + m = 0
  have h2 : ∀ x : ℝ, x = s ∨ x = r → x ^ 2 - (2 * m + 1) * x + m = 0:= by
    intro x hx
    subst r s
    rcases hx with hx | hx
    all_goals
      subst hx
      ring_nf
      field_simp
      ring_nf
  -- Specialize the quadratic equation for r
  have h3:= h2 r (by simp)
  -- Specialize the quadratic equation for s
  replace h2:= h2 s (by simp)
  -- Use r as our candidate irrational number
  use r
  refine ⟨?_, ?_, ?_⟩
  .
    -- Prove that r is irrational by contradiction
    by_contra H
    simp [Irrational] at H
    rcases H with ⟨q, hq⟩
    subst r
    -- If r is rational, then √(4m^2 + 1) must also be rational
    replace hq : ∃ r : ℚ, √(4 * m ^ 2 + 1) = r:= by
      use 2 * q - 2 * m - 1
      simp
      linarith
    -- Helper lemma: if √a is rational, then √a must be an integer
    have h4 : ∀ a : ℕ, (∃ r : ℚ, √a = r) → ∃ t : ℕ, √a = t:= by
      intro a h
      rcases h with ⟨r, hr⟩
      have h2:= Rat.mul_self_den r
      have h:= hr
      replace hr : √a ^ 2 = r ^ 2:= by rw [hr]
      field_simp at hr
      replace hr : a = r ^ 2:= by rify ; linarith
      have g2 : (↑a : ℚ).den = 1:= by exact rfl
      rw [show r * r = r ^ 2 by ring_nf] at h2
      rw [hr, h2] at g2
      simp at g2
      rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at h
      rw [g2] at h
      simp at h
      use (r.num).natAbs
      rw [show (↑(r.num).natAbs : ℝ) = (↑(r.num).natAbs : ℤ) by exact rfl]
      simp
      rw [h]
      rw [abs_of_nonneg (by rw [←h] ; positivity)]
    -- Apply the helper lemma to show √(4m^2 + 1) must be an integer
    specialize h4 (4 * m ^ 2 + 1) (by simp [hq])
    rcases h4 with ⟨t, ht⟩
    simp at ht
    replace ht : √(4 * m ^ 2 + 1) ^ 2 = t ^ 2:= by rw [ht]
    field_simp at ht
    replace ht : 4 * m ^ 2 + 1 = t ^ 2:= by
      rify
      linarith
    -- Prove that t must be greater than 2m
    have ht1 : t > 2 * m:= by
      by_contra H
      simp at H
      replace H : t ^ 2 ≤ (2 * m) ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
      linarith
    -- Prove that t must be less than 2m + 1
    have ht2 : t < 2 * m + 1:= by
      by_contra H
      simp at H
      replace H : (2 * m + 1) ^ 2 ≤ t ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
      linarith
    -- This leads to a contradiction since t cannot be both > 2m and < 2m+1
    linarith
  .
    -- Prove that r > 1
    subst r
    have g1 : √(4 * m ^ 2 + 1) ≥ 0:= by positivity
    rify at h1
    linarith
  .
    -- Prove that for all positive integers n, floor(r^n) ≡ 0 (mod m)
    -- First, establish that r + s = 2m + 1 (sum of roots)
    have h4 : r + s = 2 * m + 1:= by
      subst r s
      ring_nf
    -- Prove that s > 0
    have h5 : s > 0:= by
      subst s
      have g : (2 * m + (1 : ℝ) / 2) ^ 2 ≥ 4 * m ^ 2 + 1:= by
        rify at h1
        linarith
      replace g:= Real.sqrt_le_sqrt g
      field_simp at g
      linarith
    -- Prove that s < 1
    have h6 : s < 1:= by
      subst s
      have g : (2 * m) ^ 2 ≤ 4 * m ^ 2 + 1:= by linarith
      rify at g
      replace g : √((2 * m) ^ 2) ≤ √(4 * m ^ 2 + 1):= by exact Real.sqrt_le_sqrt g
      field_simp at g
      linarith
    -- Prove that s^n + r^n is always an integer for all n
    have h7 : ∀ n : ℕ, (∃ x : ℤ, s ^ n + r ^ n = x) ∧ (∃ y : ℤ, s ^ (n + 1) + r ^ (n + 1) = y):= by
      intro n
      induction n with
      | zero =>
        refine ⟨?_, ?_⟩
        .
          -- Base case: s^0 + r^0 = 2
          use 2
          simp
          ring_nf
        .
          -- Base case: s^1 + r^1 = 2m + 1
          use 2 * m + 1
          simp
          linarith
      | succ n ih =>
        rcases ih with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        refine ⟨⟨y, hy⟩, ?_⟩
        -- Use the recurrence relation: s^(n+2) + r^(n+2) = (2m+1)(s^(n+1) + r^(n+1)) - m(s^n + r^n)
        use (2 * m + 1) * y - m * x
        simp
        rw [show n + 1 + 1 = n + 2 by omega]
        replace h2 : s ^ n * (s ^ 2 - (2 * m + 1) * s + m) = 0:= by rw [h2] ; simp
        replace h3 : r ^ n * (r ^ 2 - (2 * m + 1) * r + m) = 0:= by rw [h3] ; simp
        rw [←hx, ←hy]
        rw [show s ^ n * (s ^ 2 - (2 * ↑m + 1) * s + ↑m) = s ^ (n + 2) - (2 * ↑m + 1) * s ^ (n + 1) + ↑m * s ^ n by ring_nf] at h2
        rw [show r ^ n * (r ^ 2 - (2 * ↑m + 1) * r + ↑m) = r ^ (n + 2) - (2 * ↑m + 1) * r ^ (n + 1) + ↑m * r ^ n by ring_nf] at h3
        linarith
    -- Extract the first part of h7 for easier use
    replace h7 : ∀ n : ℕ, ∃ x : ℤ, s ^ n + r ^ n = x:= by
      intro n
      specialize h7 n
      exact h7.1
    -- Prove that s^(n+1) + r^(n+1) ≡ 1 (mod m) for all n
    have h8 : ∀ n : ℕ, ∃ x : ℤ, s ^ (n + 1) + r ^ (n + 1) = x * m + 1:= by
      intro n
      induction n with
      | zero =>
        -- Base case: s^1 + r^1 = 2m + 1 = 2*m + 1
        use 2
        simp
        linarith
      | succ n ih =>
        rcases ih with ⟨k, hk⟩
        rw [show n + 1 + 1 = n + 2 by omega]
        specialize h7 n
        rcases h7 with ⟨x, hx⟩
        replace h2 : s ^ n * (s ^ 2 - (2 * m + 1) * s + m) = 0:= by rw [h2] ; simp
        replace h3 : r ^ n * (r ^ 2 - (2 * m + 1) * r + m) = 0:= by rw [h3] ; simp
        rw [show s ^ n * (s ^ 2 - (2 * ↑m + 1) * s + ↑m) = s ^ (n + 2) - (2 * ↑m + 1) * s ^ (n + 1) + ↑m * s ^ n by ring_nf] at h2
        rw [show r ^ n * (r ^ 2 - (2 * ↑m + 1) * r + ↑m) = r ^ (n + 2) - (2 * ↑m + 1) * r ^ (n + 1) + ↑m * r ^ n by ring_nf] at h3
        -- Use the recurrence relation to find the coefficient
        use (k * (2 * m + 1) - x + 2)
        simp
        replace h2 : s ^ (n + 2) + r ^ (n + 2) = (2 * m + 1) * (s ^ (n + 1) + r ^ (n + 1)) - m * (s ^ n + r ^ n):= by linarith
        rw [hk, hx] at h2
        linarith only [h2]
    -- Now prove the main result for any positive integer n
    intro n hn
    -- Use the previous result for n-1
    specialize h8 (n - 1)
    rw [show n - 1 + 1 = n by omega] at h8
    rcases h8 with ⟨k, hk⟩
    -- Since 0 < s < 1, we have 0 < s^n < 1
    replace h6 : s ^ n < 1:= by refine pow_lt_one₀ (by linarith) h6 (by omega)
    replace h5 : s ^ n > 0:= by positivity
    -- Prove that floor(r^n) = k*m
    have h8 : ⌊r ^ n⌋ = k * m:= by
      refine Int.floor_eq_iff.mpr ?_
      simp
      refine ⟨by linarith, by linarith⟩
    -- Since m divides floor(r^n), we have floor(r^n) ≡ 0 (mod m)
    suffices (↑m : ℤ) ∣ ⌊r ^ n⌋ by exact Dvd.dvd.modEq_zero_int this
    rw [h8]
    simp
