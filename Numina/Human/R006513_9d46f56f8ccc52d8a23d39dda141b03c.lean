import Mathlib
/- Let $d$ be a digit chosen from the set $\{1, 2, 3, 5, 6\}$. Let $N_V$ be the integer $d \cdot 5 \cdot (7+1)^2$. Let $C_3, C_2, C_1, C_0$ be the base-7 digits of $N_V$, meaning $N_V = C_637909 \cdot 7^3 + C_637909 \cdot 7^2 + C_637909 \cdot 7 + C_0$, where $0 \le C_i < 7$. (For example, if $d=1$, $N_V = 320$, so $C_3=0, C_2=6, C_1=3, C_0=5$. If $d=2$, $N_V=640$, so $C_3=1, C_2=6, C_1=0, C_0=3$.)
In what base $b$ does the equation $(d \cdot b + d)(5 \cdot b + 5) = C_637909 b^3 + C_637909 b^2 + C_637909 b + C_0$ hold, assuming $b$ is an integer satisfying $b > \max(\{d, 5, C_0, C_1, C_2, C_3\})$? Show the answer is $b=7$. -/
theorem number_theory_637909 (d c0 c1 c2 c3 n b : ℕ) (hd : d ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ)) (hn : n = d * 5 * (7 + 1) ^ 2) (h : n = c3 * 7 ^ 3 + c2 * 7 ^ 2 + c1 * 7 + c0) (hc0 : c0 < 7) (hc1 : c1 < 7) (hc2 : c2 < 7) (hc3 : c3 < 7) (hb : b > d ∧ b > 5 ∧ b > c0 ∧ b > c1 ∧ b > c2 ∧ b > c3) : (d * b + d) * (5 * b + 5) = c3 * b ^ 3 + c2 * b ^ 2 + c1 * b + c0 ↔ b = 7:= by
  -- Split the biconditional into two directions
  constructor
  .
    -- Forward direction: if equation holds, then b = 7
    intro h1
    -- Case analysis on the digit d
    fin_cases hd
    .
      -- Case d = 1: N_V = 320, so c3=0, c2=6, c1=3, c0=5
      simp at hn
      subst n
      have g3 : c3 = 0:= by omega
      have g2 : c2 = 6:= by omega
      have g1 : c1 = 3:= by omega
      have g0 : c0 = 5:= by omega
      subst c0 c1 c2 c3
      -- Simplify the equation to b^2 = b*7
      ring_nf at h1
      replace h1 : b * b = b * 7:= by linarith
      replace hb : b > 0:= by omega
      -- Since b > 0, we can cancel b to get b = 7
      exact Nat.eq_of_mul_eq_mul_left hb h1
    .
      -- Case d = 2: N_V = 640, so c3=1, c2=6, c1=0, c0=3
      simp at hn
      subst n
      have g3 : c3 = 1:= by omega
      have g2 : c2 = 6:= by omega
      have g1 : c1 = 0:= by omega
      have g0 : c0 = 3:= by omega
      subst c0 c1 c2 c3
      -- Simplify to cubic equation
      ring_nf at h1
      replace h1 : b ^ 3 = 4 * b ^ 2 + 20 * b + 7:= by linarith
      -- Convert to integer arithmetic for factorization
      zify at h1
      replace h1 : ((b : ℤ) - 7) * (b ^ 2 + 3 * b + 1) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      .
        -- First factor: b - 7 = 0, so b = 7
        zify
        linarith
      .
        -- Second factor: b^2 + 3b + 1 = 0, but this has no positive integer solutions
        replace h1 : b ^ 2 + 3 * b + 1 = 0:= by
          zify
          exact h1
        omega
    .
      -- Case d = 3: N_V = 960, so c3=2, c2=5, c1=4, c0=1
      simp at hn
      subst n
      have g3 : c3 = 2:= by omega
      have g2 : c2 = 5:= by omega
      have g1 : c1 = 4:= by omega
      have g0 : c0 = 1:= by omega
      subst c0 c1 c2 c3
      -- Simplify to cubic equation
      ring_nf at h1
      replace h1 : b ^ 3 = 5 * b ^ 2 + 13 * b + 7:= by linarith
      -- Factor as (b-7)(b^2+2b+1) = 0
      zify at h1
      replace h1 : ((b : ℤ) - 7) * (b ^ 2 + 2 * b + 1) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      .
        -- First factor: b - 7 = 0, so b = 7
        zify
        linarith
      .
        -- Second factor: b^2 + 2b + 1 = 0, but this has no positive integer solutions
        replace h1 : b ^ 2 + 2 * b + 1 = 0:= by
          zify
          linarith
        omega
    .
      -- Case d = 4: N_V = 1280, so c3=3, c2=5, c1=0, c0=6
      simp at hn
      subst n
      have g3 : c3 = 3:= by omega
      have g2 : c2 = 5:= by omega
      have g1 : c1 = 0:= by omega
      have g0 : c0 = 6:= by omega
      subst c0 c1 c2 c3
      -- Simplify to cubic equation
      ring_nf at h1
      replace h1 : 3 * b ^ 3 = 15 * b ^ 2 + 40 * b + 14:= by linarith
      -- Factor as (b-7)(3b^2+6b+2) = 0
      zify at h1
      replace h1 : ((b : ℤ) - 7) * (3 * b ^ 2 + 6 * b + 2) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      .
        -- First factor: b - 7 = 0, so b = 7
        zify
        linarith
      .
        -- Second factor: 3b^2 + 6b + 2 = 0, but this has no positive integer solutions
        replace h1 : 3 * b ^ 2 + 6 * b + 2 = 0:= by
          zify
          linarith
        omega
    .
      -- Case d = 5: N_V = 1600, so c3=4, c2=4, c1=4, c0=4
      simp at hn
      subst n
      have g3 : c3 = 4:= by omega
      have g2 : c2 = 4:= by omega
      have g1 : c1 = 4:= by omega
      have g0 : c0 = 4:= by omega
      subst c0 c1 c2 c3
      -- Simplify to cubic equation
      ring_nf at h1
      replace h1 : 4 * b ^ 3 = 21 * b ^ 2 + 46 * b + 21:= by linarith
      -- Factor as (b-7)(4b^2+7b+3) = 0
      zify at h1
      replace h1 : ((b : ℤ) - 7) * (4 * b ^ 2 + 7 * b + 3) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      .
        -- First factor: b - 7 = 0, so b = 7
        zify
        linarith
      .
        -- Second factor: 4b^2 + 7b + 3 = 0, but this has no positive integer solutions
        replace h1 : 4 * b ^ 2 + 7 * b + 3 = 0:= by
          zify
          linarith
        omega
    .
      -- Case d = 6: N_V = 1920, so c3=5, c2=4, c1=1, c0=2
      simp at hn
      subst n
      have g3 : c3 = 5:= by omega
      have g2 : c2 = 4:= by omega
      have g1 : c1 = 1:= by omega
      have g0 : c0 = 2:= by omega
      subst c0 c1 c2 c3
      -- Simplify to cubic equation
      ring_nf at h1
      replace h1 : 5 * b ^ 3 = 26 * b ^ 2 + 59 * b + 28:= by linarith
      -- Factor as (b-7)(5b^2+9b+4) = 0
      zify at h1
      replace h1 : ((b : ℤ) - 7) * (5 * b ^ 2 + 9 * b + 4) = 0:= by linarith
      simp at h1
      rcases h1 with h1 | h1
      .
        -- First factor: b - 7 = 0, so b = 7
        zify
        linarith
      .
        -- Second factor: 5b^2 + 9b + 4 = 0, but this has no positive integer solutions
        replace h1 : 5 * b ^ 2 + 9 * b + 4 = 0:= by
          zify
          linarith
        omega
  .
    -- Reverse direction: if b = 7, then the equation holds
    intro h
    subst b
    -- Substitute b = 7 and use the definition of n
    rw [←h, hn]
    -- Simplify to show both sides are equal
    ring_nf
