import Mathlib
/- Define the sequence of positive integers $a_{n}$ recursively by $a_{1}=7$ and $a_{n}=7^{a_{n-1}}$ for all $n \geq 2$. Determine the last two digits of $a_{2007}$. -/
theorem algebra_608187 (a : ℕ → ℕ) (h0 : a 0 = 7) (h1 : ∀ n : ℕ, a (n + 1) = 7 ^ a n) :
a 2006 ≡ 43 [ZMOD 100]:= by
  -- First, we prove that for all n, a_n ≡ 1 (mod 2)
  have h2 : ∀ n : ℕ, a n ≡ 1 [ZMOD 2]:= by
    intro n
    by_cases hn : n = 0
    .
      subst n
      rw [h0]
      simp
      rfl
    .
      rw [show n = n - 1 + 1 by omega, h1 (n - 1)]
      simp
      -- Since 7 ≡ 1 (mod 2), we have 7^k ≡ 1^k ≡ 1 (mod 2) for any k
      have g1 : 7 ≡ 1 [ZMOD 2]:= by rfl
      replace g1 : 7 ^ a (n - 1) ≡ 1 ^ a (n - 1) [ZMOD 2]:= by exact Int.ModEq.pow (a (n - 1)) g1
      simp at g1
      exact g1

  -- Prove that a_2004 > 0, which will be needed later
  have g2 : a 2004 > 0:= by
    rw [show 2004 = 2003 + 1 by omega, h1 2003]
    simp

  -- Prove that a_2005 ≡ 3 (mod 4)
  have h3 : a 2005 ≡ 3 [ZMOD 4]:= by
    rw [show 2005 = 2004 + 1 by omega, h1 2004]
    simp
    -- Since 7 ≡ -1 (mod 4), we have 7^k ≡ (-1)^k (mod 4)
    have g1 : 7 ≡ -1 [ZMOD 4]:= by rfl
    replace g1 : 7 ^ a 2004 ≡ (-1) ^ a 2004 [ZMOD 4]:= by exact Int.ModEq.pow (a 2004) g1

    -- Use the fact that a_2004 is odd (from h2) to determine (-1)^a_2004
    specialize h2 2004
    replace h2 : 2 ∣ (↑(a 2004) : ℤ) - 1:= by exact Int.dvd_sub_of_emod_eq h2
    replace h2 : 2 ∣  a 2004 - 1:= by
      zify
      have g3 : a 2004 - 1 + 1 = a 2004:= by omega
      zify at g3
      replace g3 : (↑(a 2004 - 1) : ℤ) = ↑(a 2004) - 1:= by omega
      rw [g3]
      exact h2
    replace h2 : ∃ k : ℕ, a 2004 - 1 = 2 * k:= by exact h2
    rcases h2 with ⟨k, hk⟩
    replace hk : a 2004 = 2 * k + 1:= by omega
    replace hk : (-1 : ℤ) ^ a 2004 = -1:= by
      rw [hk]
      rw [show (-1 : ℤ) ^ (2 * k + 1) = (-1) ^ (2 * k) * (-1) by ring]
      simp
    rw [hk] at g1
    exact g1

  -- From a_2005 ≡ 3 (mod 4), we get 4 | (a_2005 - 3)
  replace h3 : 4 ∣ (↑(a 2005) : ℤ) - 3:= by exact Int.dvd_sub_of_emod_eq h3

  -- Prove that a_2005 ≥ 7 (will be used for algebraic manipulations)
  replace g2 : a 2005 ≥ 7:= by
    rw [show 2005 = 2004 + 1 by omega, h1 2004]
    replace g2 : a 2004 ≥ 1:= by omega
    refine Bound.le_self_pow_of_pos (by omega) g2

  -- Algebraic manipulations to work with a_2005 - 3
  replace g2 : a 2005 - 3 + 3 = a 2005:= by omega
  zify at g2
  replace g2 : (↑(a 2005 - 3) : ℤ) = ↑(a 2005) - 3:= by omega
  rw [←g2] at h3
  replace h3 : 4 ∣ a 2005 - 3:= by
    zify
    exact h3

  -- Express a_2005 as 4k + 3 for some natural number k
  replace h3 : ∃ k : ℕ, a 2005 - 3 = 4 * k:= by exact h3
  rcases h3 with ⟨k, hk⟩
  replace hk : a 2005 = 4 * k + 3:= by omega

  -- Calculate a_2006 using the recursive definition and the form of a_2005
  rw [show 2006 = 2005 + 1 by omega, h1 2005]
  rw [hk]
  simp

  -- Use properties of exponents to simplify 7^(4k+3)
  rw [show (7 : ℤ) ^ (4 * k + 3) = 7 ^ (4 * k) * 7 ^ 3 by ring]
  rw [show (7 : ℤ) ^ (4 * k) = (7 ^ 4) ^ k by exact pow_mul 7 4 k]

  -- Use the fact that 7^4 ≡ 1 (mod 100) to simplify further
  have h3 : 7 ^ 4 ≡ 1 [ZMOD 100]:= by rfl
  replace h3 : (7 ^ 4) ^ k ≡ 1 ^ k [ZMOD 100]:= by exact Int.ModEq.pow k h3
  simp at h3
  simp

  -- Complete the proof by showing that a_2006 ≡ 343 ≡ 43 (mod 100)
  replace h3 : 2401 ^ k * 343 ≡ 1 * 343 [ZMOD 100]:= by exact Int.ModEq.mul h3 (by rfl)
  exact h3
