import Mathlib
/- Let $k$ be an integer such that $3 \le k \le 9$. Let $a$ be a two-digit natural number (meaning $10 \le a < 100$) and $b$ be a positive natural number. Suppose that the product of $a$ and $b$ is equal to $41k$. Let $a_{rev}$ be the number obtained by reversing the digits of $a$ (for example, if $a=23$, $a_{rev}=32$; if $a=50$, $a_{rev}=5$). Show that the product of $a_{rev}$ and $b$ is equal to $14k$. -/
theorem number_theory_636941 (k b x1 x2 : ℕ) (hx1 : 1 ≤ x1) (hx2 : x1 ≤ 9) (hx3 : x2 ≤ 9) (hk1 : 3 ≤ k) (hk2 : k ≤ 9) (h : (10 * x1 + x2) * b = 41 * k) : (10 * x2 + x1) * b = 14 * k:= by

  -- First, we establish that 41 divides the product (10x1 + x2)b
  have h1 : 41 ∣ (10 * x1 + x2) * b:= by rw [h] ; simp

  -- 41 is a prime number
  have g1 : Nat.Prime 41:= by norm_num

  -- By prime divisibility property, either 41 divides (10x1 + x2) or 41 divides b
  replace h1 : 41 ∣ 10 * x1 + x2 ∨ 41 ∣ b:= by exact (Nat.Prime.dvd_mul g1).mp h1

  -- Case analysis on which factor 41 divides
  rcases h1 with h1 | h1
  .
    -- Case 1: 41 divides (10x1 + x2)
    rcases h1 with ⟨c, hc⟩

    -- Given the constraints on x1 and x2, c can only be 1 or 2
    have hc1 : c = 1 ∨ c = 2:= by omega
    rcases hc1 with hc1 | hc1
    .
      -- Subcase: c = 1
      subst c
      rw [hc] at h
      have h1 : x1 = 4:= by omega
      have h2 : x2 = 1:= by omega
      simp at h
      subst b x1 x2
      simp
    .
      -- Subcase: c = 2
      subst c
      rw [hc] at h
      have h1 : x1 = 8:= by omega
      have h2 : x2 = 2:= by omega
      subst x1 x2
      omega
  .
    -- Case 2: 41 divides b
    rcases h1 with ⟨c, hc⟩
    subst b

    -- Show that c must be at least 1
    have hc : c ≥ 1:= by
      by_contra H
      simp at H
      subst c
      simp at h
      linarith

    -- Use this to derive a contradiction with the given bounds
    replace hc : (10 * x1 + x2) * c ≥ 10 * x1 + x2:= by exact Nat.le_mul_of_pos_right (10 * x1 + x2) hc
    linarith
