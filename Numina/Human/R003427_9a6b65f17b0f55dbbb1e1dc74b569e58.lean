import Mathlib
/- Problem 4. Find all pairs of natural numbers $x$ and $y$, such that the ratio $\frac{x y^{3}}{x+y}$ is a prime number. -/
theorem number_theory_179916 : {(x, y) : ℕ × ℕ | ∃ p : ℕ, Nat.Prime p ∧ (↑p : ℚ) = (x * y ^ 3) / (x + y)} = {(14, 2)}:= by
  ext ⟨x, y⟩
  constructor
  .
    -- Forward direction: if xy³/(x+y) is prime, then (x,y) = (14,2)
    intro h
    simp at h
    rcases h with ⟨p, hp, h⟩
    -- Prime p is greater than 1
    have hpge : p > 1:= by exact Nat.Prime.one_lt hp
    -- x must be positive (otherwise the ratio would be 0)
    have hx : x > 0 := by
      by_contra H
      simp at H
      subst x
      simp at h
      linarith
    -- y must be positive (otherwise the ratio would be 0)
    have hy : y > 0 := by
      by_contra H
      simp at H
      subst y
      simp at h
      linarith
    -- Clear denominators to get p(x+y) = xy³
    field_simp at h
    replace h : p * (x + y) = x * y ^ 3:= by qify ; linarith
    -- p divides xy³
    have h1 : p ∣ x * y ^ 3:= by rw [←h] ; simp
    -- Since p is prime, p divides x or p divides y³
    replace h1 : p ∣ x ∨ p ∣ y ^ 3:= by exact (Nat.Prime.dvd_mul hp).mp h1
    rcases h1 with h1 | h1
    .
      -- Case 1: p divides x
      rcases h1 with ⟨k, hk⟩
      subst x
      rw [show p * k * y ^ 3 = p * (k * y ^ 3) by ring] at h
      -- Simplify to get pk + y = ky³
      replace h : p * k + y = k * y ^ 3:= by
        replace hpge : p ≠ 0:= by omega
        exact (Nat.mul_right_inj hpge).mp h
      -- y³ > p (otherwise we get a contradiction)
      have h1 : y ^ 3 > p:= by
        by_contra H
        simp at H
        replace H : k * y ^ 3 ≤ k * p:= by exact Nat.mul_le_mul_left k H
        linarith
      -- Let t = y³ - p
      set t:= y ^ 3 - p with ht
      clear_value t
      replace ht : y ^ 3 = t + p:= by omega
      rw [ht] at h
      -- This gives us y = kt
      replace h : y = k * t:= by linarith
      -- t divides y
      have h1 : t ∣ y:= by rw [h] ; simp
      -- Therefore t divides y³
      replace h1 : t ∣ y ^ 3:= by refine Dvd.dvd.pow h1 (by omega)
      have h2 : t ∣ t:= by simp
      rw [ht] at h1
      -- t divides p
      replace h2 : t ∣ p:= by exact (Nat.dvd_add_iff_right h2).mpr h1
      -- Since p is prime, t = 1 or t = p
      replace h2 : t = 1 ∨ t = p:= by exact (Nat.dvd_prime hp).mp h2
      clear h1
      rcases h2 with h2 | h2
      .
        -- Subcase: t = 1, so y³ = p + 1
        subst t
        simp at h
        set z:= y - 1 with hz
        clear_value z
        replace hz : y = z + 1:= by omega
        rw [hz] at ht
        -- This gives us z(z² + 3z + 3) = p
        replace ht : z * (z ^ 2 + 3 * z + 3) = p:= by linarith
        -- z divides p
        have h2 : z ∣ p:= by rw [←ht] ; simp
        -- Since p is prime, z = 1 or z = p
        replace h2 : z = 1 ∨ z = p:= by exact (Nat.dvd_prime hp).mp h2
        rcases h2 with h2 | h2
        .
          -- If z = 1, then y = 2, p = 7, k = 1, x = 14
          subst z
          simp at ht
          rw [←ht]
          simp at hz
          subst y k
          simp
        .
          -- If z = p, we get a contradiction
          subst z
          ring_nf at ht
          omega
      .
        -- Subcase: t = p, so y³ = 2p
        subst t y
        ring_nf at ht
        rw [show k ^ 3 * p ^ 3 = p * (k ^ 3 * p ^ 2) by ring] at ht
        -- This gives us k³p² = 2
        replace ht : k ^ 3 * p ^ 2 = 2:= by
          replace hpge : p > 0:= by omega
          exact Eq.symm (Nat.eq_of_mul_eq_mul_left hpge (id (Eq.symm ht)))
        -- Since p is prime and divides 2, we must have p = 2
        have h2 : p = 2:= by
          have g1 : Nat.Prime 2:= by norm_num
          replace ht : p ∣ 2:= by rw [←ht] ; rw [show k ^ 3 * p ^ 2 = p * (k ^ 3 * p) by ring] ; simp
          exact (Nat.prime_dvd_prime_iff_eq hp g1).mp ht
        subst p
        ring_nf at ht
        simp at hx
        -- But then k³ = 1/2, which is impossible for natural k
        replace hx : k ^ 3 > 0:= by positivity
        linarith
    .
      -- Case 2: p divides y³, so p divides y
      replace h1 : p ∣ y:= by exact Nat.Prime.dvd_of_dvd_pow hp h1
      rcases h1 with ⟨k, hk⟩
      subst y
      ring_nf at h
      replace hpge : p ≥ 2:= by omega
      -- k³ > 0 since y > 0
      have g1 : k ^ 3 > 0:= by
        by_contra H
        simp at H
        subst k
        simp at hy
      -- pk³ ≥ 2
      replace g1 : p * k ^ 3 ≥ 2:= by
        replace g1 : k ^ 3 ≥ 1:= by omega
        exact le_mul_of_le_of_one_le hpge g1
      -- This leads to p²xk³ > px, but also p²xk³ = px + pk, giving a contradiction
      replace g1 : p * x * (p * k ^ 3) ≥ p * x * 2:= by exact Nat.mul_le_mul_left (p * x) g1
      have g3 : p * x > 0:= by positivity
      replace g1 : p * x * (p * k ^ 3) > p * x:= by linarith
      replace g2 : x * k ^ 2 ≥ 1:= by
        by_contra H
        simp at H
        rcases H with H | H
        .
          linarith
        .
          subst k
          simp at hy
      replace g2 : p ^ 2 * k * (x * k ^ 2) ≥ p ^ 2 * k:= by exact Nat.le_mul_of_pos_right (p ^ 2 * k) g2
      replace hpge : p * (p ^ 2 * x * k ^ 3) ≥ 2 * (p ^ 2 * x * k ^ 3):= by exact Nat.mul_le_mul_right (p ^ 2 * x * k ^ 3) hpge
      linarith
  .
    -- Backward direction: if (x,y) = (14,2), then xy³/(x+y) is prime
    intro h
    simp at h
    rcases h with ⟨hx, hy⟩
    subst x y
    simp
    -- Verify that 14·2³/(14+2) = 112/16 = 7, which is prime
    norm_num
    use 7
    simp
    decide
