import Mathlib
/- $a_{n}$ is the last digit of $1+2+\ldots+n$. Find $a_{1}+a_{2}+\ldots+a_{1992}$. -/
theorem number_theory_604464 (a : ℕ → ℕ) (hn : ∀ n > 0, a n = (∑ i in Finset.range n, (i + 1)) % 10) : ∑ i in Finset.range 1992, a (i + 1) = 6984:= by
  -- Prove that 2 * (1+2+...+n) = n(n+1)
  have h1 : ∀ n : ℕ, 2 * ∑ i in Finset.range n, (i + 1) = (n + 1) * n:= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show 2 * (∑ x ∈ Finset.range n, (x + 1) + (n + 1)) = 2 * (∑ x ∈ Finset.range n, (x + 1)) + 2 * (n + 1) by ring]
      rw [ih]
      linarith
  -- Rewrite the sum formula as (n+1)*n/2
  replace h1 : ∀ n : ℕ, ∑ i in Finset.range n, (i + 1) = (n + 1) * n / 2:= by
    intro n
    specialize h1 n
    rw [←h1]
    omega
  -- Rewrite the definition of a_n using the sum formula
  replace hn : ∀ n > 0, a n = ((n + 1) * n / 2) % 10:= by
    intro n h
    rw [hn n h, h1 n]
  clear h1
  -- Prove that the sum of a_i for i from 1 to 20n equals 70n
  have h1 : ∀ n : ℕ,  ∑ i ∈ Finset.range (20 * n), a (i + 1) = 70 * n:= by
    intro n
    induction n with
    | zero =>
      simp [Finset.sum_range_succ]
    | succ n ih =>
      -- Prove that a_(m+i+1) = a_(i+1) when 20 divides m
      have h2 : ∀ i m : ℕ, 20 ∣ m → a (m + i + 1) = a (i + 1):= by
        intro i m hm
        simp [hn]
        suffices (m + i + 1 + 1) * (m + i + 1) / 2 ≡ (i + 1 + 1) * (i + 1) / 2 [MOD 10] by exact this
        replace hm : ∃ t : ℕ, m = 20 * t:= by exact hm
        rcases hm with ⟨t, ht⟩
        subst m
        -- Case analysis based on whether i is odd or even
        by_cases hi : Odd i
        .
          -- Case: i is odd
          simp [Odd] at hi
          rcases hi with ⟨k, hk⟩
          subst i
          rw [show (20 * t + (2 * k + 1) + 1 + 1) * (20 * t + (2 * k + 1) + 1) = (20 * t + 2 * k + 3) * (10 * t + k + 1) * 2 by ring]
          rw [show (2 * k + 1 + 1 + 1) * (2 * k + 1 + 1) = (2 * k + 3) * (k + 1) * 2 by ring]
          rw [show (20 * t + 2 * k + 3) * (10 * t + k + 1) * 2 / 2 = (20 * t + 2 * k + 3) * (10 * t + k + 1) by omega]
          rw [show (2 * k + 3) * (k + 1) * 2 / 2 = (2 * k + 3) * (k + 1) by omega]
          -- Prove congruence modulo 10
          have g1 : 10 ≡ 0 [MOD 10]:= by rfl
          have g2 : 10 * t ≡ 0 * t [MOD 10]:= by exact g1.mul_right t
          replace g1 : 10 * (2 * t) ≡ 0 * (2 * t) [MOD 10]:= by exact g1.mul_right (2 * t)
          simp at g1 g2
          rw [show 10 * (2 * t) = 20 * t by ring] at g1
          rw [show (20 * t + 2 * k + 3) * (10 * t + k + 1) = (20 * t + (2 * k + 3)) * (10 * t + (k + 1)) by ring]
          replace g1 : 20 * t + (2 * k + 3) ≡ 0 + (2 * k + 3) [MOD 10]:= by exact g1.add_right (2 * k + 3)
          replace g2 : 10 * t + (k + 1) ≡ 0 + (k + 1) [MOD 10]:= by exact g2.add_right (k + 1)
          simp at g1 g2
          exact Nat.ModEq.mul g1 g2
        .
          -- Case: i is even
          simp at hi
          simp [Even] at hi
          rcases hi with ⟨k, hk⟩
          rw [show k + k = 2 * k by ring] at hk
          subst i
          rw [show (20 * t + (2 * k) + 1 + 1) * (20 * t + (2 * k) + 1) = (10 * t + k + 1) * (20 * t + 2 * k + 1) * 2 by ring]
          rw [show (2 * k + 1 + 1) * (2 * k + 1) = (k + 1) * (2 * k + 1) * 2 by ring]
          have g1 : 10 ≡ 0 [MOD 10]:= by rfl
          have g2 : 10 * t ≡ 0 * t [MOD 10]:= by exact g1.mul_right t
          replace g1 : 10 * (2 * t) ≡ 0 * (2 * t) [MOD 10]:= by exact g1.mul_right (2 * t)
          simp at g1 g2
          rw [show 10 * (2 * t) = 20 * t by ring] at g1
          rw [show (10 * t + k + 1) * (20 * t + 2 * k + 1) = (10 * t + (k + 1)) * (20 * t + (2 * k + 1)) by ring]
          replace g1 : 20 * t + (2 * k + 1) ≡ 0 + (2 * k + 1) [MOD 10]:= by exact g1.add_right (2 * k + 1)
          replace g2 : 10 * t + (k + 1) ≡ 0 + (k + 1) [MOD 10]:= by exact g2.add_right (k + 1)
          simp at g1 g2
          rw [show (10 * t + (k + 1)) * (20 * t + (2 * k + 1)) * 2 / 2  = (10 * t + (k + 1)) * (20 * t + (2 * k + 1)) by omega]
          rw [show (k + 1) * (2 * k + 1) * 2 / 2 = (k + 1) * (2 * k + 1) by omega]
          exact Nat.ModEq.mul g2 g1
      -- Expand the sum for the inductive step
      rw [show 20 * (n + 1) = 20 * n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
      simp [Finset.sum_range_succ]
      rw [ih]
      -- Apply the periodicity property to each term
      rw [h2 0 (20 * n) (by omega)]
      rw [h2 1 (20 * n) (by omega)]
      rw [h2 2 (20 * n) (by omega)]
      rw [h2 3 (20 * n) (by omega)]
      rw [h2 4 (20 * n) (by omega)]
      rw [h2 5 (20 * n) (by omega)]
      rw [h2 6 (20 * n) (by omega)]
      rw [h2 7 (20 * n) (by omega)]
      rw [h2 8 (20 * n) (by omega)]
      rw [h2 9 (20 * n) (by omega)]
      rw [h2 10 (20 * n) (by omega)]
      rw [h2 11 (20 * n) (by omega)]
      rw [h2 12 (20 * n) (by omega)]
      rw [h2 13 (20 * n) (by omega)]
      rw [h2 14 (20 * n) (by omega)]
      rw [h2 15 (20 * n) (by omega)]
      rw [h2 16 (20 * n) (by omega)]
      rw [h2 17 (20 * n) (by omega)]
      rw [h2 18 (20 * n) (by omega)]
      rw [h2 19 (20 * n) (by omega)]
      simp [hn]
      linarith
  -- Apply the formula for the first 1980 terms (99 * 20)
  specialize h1 99
  rw [show 20 * 99 = 1980 by ring] at h1
  -- Break down 1992 as 1980 + 12
  rw [show 1992 = 1980 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
  set m:= 1980 with hm
  clear_value m
  simp [Finset.sum_range_succ]
  rw [h1]
  subst m
  simp [hn]
