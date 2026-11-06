import Mathlib
/- 1. Given the sequence $\left\{a_{n}\right\}$ satisfies:
$$
a_{1}=1, a_{n}=5 a_{n-1}+3^{n-1}(n \geqslant 2) \text {. }
$$

Find $a_{n}$ and the highest power of 2 that divides $a_{k}\left(k=2^{2019}\right)$ -/
theorem algebra_280231 (a : ℕ → ℤ) (h1 : a 0 = 1) (h2 : ∀ n : ℕ, a (n + 1) = 5 * a n + 3 ^ (n + 1)) : (∀ n : ℕ, a n = (5 ^ (n + 1) - 3 ^ (n + 1)) / 2) ∧ IsGreatest {k : ℕ | 2 ^ k ∣ a (2 ^ 2019 - 1)} 2021:= by
  -- Key lemma: 2*a_n = 5^{n+1} - 3^{n+1}
  have h3 : ∀ n : ℕ, 2 * a n = 5 ^ (n + 1) - 3 ^ (n + 1):= by
    intro n
    -- Proof by induction on n
    induction n with
    -- Base case: n = 0
    | zero =>
      rw [h1]
      simp
    -- Inductive step: assume true for n, prove for n+1
    | succ n ih =>
      rw [h2 n]
      ring_nf
      rw [show a n * 10 = 5 * (2 * a n) by ring]
      rw [ih]
      ring_nf
  constructor
  -- First part: prove the explicit formula for a_n
  .
    intro n
    specialize h3 n
    -- Use the fact that 2*a_n = 5^{n+1} - 3^{n+1} to get a_n = (5^{n+1} - 3^{n+1})/2
    refine Int.eq_ediv_of_mul_eq_right (by omega) h3
  -- Second part: prove the highest power of 2 dividing a_{2^2019-1} is 2^2021
  .
    set t:= 2019 with ht
    clear_value t
    -- General result: the highest power of 2 dividing a_{2^{n+1}-1} is 2^{n+3}
    have h4 : ∀ n : ℕ, IsGreatest {k | 2 ^ k ∣ a (2 ^ (n + 1) - 1)} (n + 3):= by
      intro n
      -- Proof by induction on n
      induction n with
      -- Base case: n = 0, prove that 2^3 is the highest power of 2 dividing a_1
      | zero =>
        simp
        constructor
        -- Prove that 2^3 divides a_1
        .
          simp
          rw [h2 0, h1]
          simp
        -- Prove that no higher power of 2 divides a_1
        .
          simp [upperBounds]
          intro k hk
          by_contra H
          simp at H
          set k1:= k - 4 with hk1
          clear_value k1
          replace hk1 : k = k1 + 4:= by omega
          subst k
          rw [h2 0, h1] at hk
          ring_nf at hk
          have g1 : (16 : ℤ) ∣ 2 ^ k1 * 16:= by simp
          replace hk : (16 : ℤ) ∣ 8:= by exact Int.dvd_trans g1 hk
          omega
      -- Inductive step: assume true for n, prove for n+1
      | succ n ih =>
        rcases ih with ⟨ih1, ih2⟩
        simp [upperBounds] at ih2
        simp at ih1
        constructor
        -- Prove that 2^{n+4} divides a_{2^{n+2}-1}
        .
          simp
          -- Use the fact that 2 * 2^{n+4} divides 2 * a_{2^{n+2}-1}
          suffices 2 * 2 ^ (n + 1 + 3) ∣ 2 * a (2 ^ (n + 1 + 1) - 1) by exact Int.dvd_of_mul_dvd_mul_left (by omega) this
          replace ih1 : 2 * 2 ^ (n + 3) ∣ 2 * a (2 ^ (n + 1) - 1):= by exact Int.mul_dvd_mul_left 2 ih1
          rw [h3 (2 ^ (n + 1) - 1)] at ih1
          rw [h3 (2 ^ (n + 1 + 1) - 1)]
          have g1 : 2 ^ (n + 1) > 0:= by positivity
          have g2 : 2 ^ (n + 1 + 1) > 0:= by positivity
          rw [show 2 ^ (n + 1) - 1 + 1 = 2 ^ (n + 1) by omega] at ih1
          rw [show 2 ^ (n + 1 + 1) - 1 + 1 = 2 ^ (n + 1 + 1) by omega]
          rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 by ring]
          rw [show (2 : ℤ) * 2 ^ (n + 1 + 3) = 2 * (2 * 2 ^ (n + 3)) by ring_nf]
          -- Use the identity x^{2m} - y^{2m} = (x^m + y^m)(x^m - y^m)
          rw [show (5 : ℤ) ^ (2 ^ (n + 1) * 2) = (5 ^ (2 ^ (n + 1))) ^ 2 by ring_nf]
          rw [show (3 : ℤ) ^ (2 ^ (n + 1) * 2) = (3 ^ (2 ^ (n + 1))) ^ 2 by ring_nf]
          rw [show ((5 : ℤ) ^ 2 ^ (n + 1)) ^ 2 - (3 ^ 2 ^ (n + 1)) ^ 2 = (5 ^ 2 ^ (n + 1) + 3 ^ 2 ^ (n + 1)) * (5 ^ 2 ^ (n + 1) - 3 ^ 2 ^ (n + 1)) by ring_nf]
          -- Prove that 2 divides 5^{2^{n+1}} + 3^{2^{n+1}}
          suffices (2 : ℤ) ∣ 5 ^ 2 ^ (n + 1) + 3 ^ 2 ^ (n + 1) by exact Int.mul_dvd_mul this ih1
          -- Since 5 and 3 are odd, their powers are odd, so their sum is even
          replace g1 : Odd (5 : ℤ):= by decide
          replace g2 : Odd (3 : ℤ):= by decide
          replace g1 : Odd ((5 : ℤ) ^ 2 ^ (n + 1)):= by exact Odd.pow g1
          replace g2 : Odd ((3 : ℤ) ^ 2 ^ (n + 1)):= by exact Odd.pow g2
          replace g1 : Even ((5 : ℤ) ^ 2 ^ (n + 1) + 3 ^ 2 ^ (n + 1)):= by exact Odd.add_odd g1 g2
          exact even_iff_two_dvd.mp g1
        -- Prove that no higher power of 2 divides a_{2^{n+2}-1}
        .
          simp [upperBounds]
          intro k hk
          replace hk : 2 * 2 ^ k ∣ 2 * a (2 ^ (n + 1 + 1) - 1):= by exact Int.mul_dvd_mul_left 2 hk
          rw [h3 (2 ^ (n + 1 + 1) - 1)] at hk
          have g1 : 2 ^ (n + 1 + 1) > 0:= by positivity
          rw [show 2 ^ (n + 1 + 1) - 1 + 1 = 2 ^ (n + 1 + 1) by omega] at hk
          rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 by ring_nf] at hk
          rw [show (5 : ℤ) ^ (2 ^ (n + 1) * 2) = (5 ^ (2 ^ (n + 1))) ^ 2 by ring_nf] at hk
          rw [show (3 : ℤ) ^ (2 ^ (n + 1) * 2) = (3 ^ (2 ^ (n + 1))) ^ 2 by ring_nf] at hk
          rw [show ((5 : ℤ) ^ 2 ^ (n + 1)) ^ 2 - (3 ^ 2 ^ (n + 1)) ^ 2 = (5 ^ 2 ^ (n + 1) + 3 ^ 2 ^ (n + 1)) * (5 ^ 2 ^ (n + 1) - 3 ^ 2 ^ (n + 1)) by ring_nf] at hk
          set s:= (5 : ℤ) ^ 2 ^ (n + 1) + 3 ^ 2 ^ (n + 1) with hs
          clear_value s
          -- Prove that s ≡ 2 (mod 4)
          have hs1 : s ≡ 2 [ZMOD 4]:= by
            -- 5 ≡ 1 (mod 4)
            have g1 : 5 ≡ 1 [ZMOD 4]:= by rfl
            replace g1 : 5 ^ 2 ^ (n + 1) ≡ 1 ^ (2 ^ (n + 1)) [ZMOD 4]:= by exact Int.ModEq.pow (2 ^ (n + 1)) g1
            simp at g1
            -- 3 ≡ -1 (mod 4)
            have g2 : 3 ≡ -1 [ZMOD 4]:= by rfl
            replace g2 : 3 ^ 2 ^ (n + 1) ≡ (-1) ^ (2 ^ (n + 1)) [ZMOD 4]:= by exact Int.ModEq.pow (2 ^ (n + 1)) g2
            -- 2^{n+1} is even, so (-1)^{2^{n+1}} = 1
            have g3 : Even (2 ^ (n + 1)):= by
              have g3 : Even 2:= by decide
              refine (Nat.even_pow' (by omega)).mpr g3
            rw [show (-1 : ℤ) ^ (2 ^ (n + 1)) = 1 by exact Even.neg_one_pow g3] at g2
            rw [show (2 : ℤ) = 1 + 1 by ring_nf]
            subst s
            exact Int.ModEq.add g1 g2
          -- Since s ≡ 2 (mod 4), we have 4 | (s - 2)
          replace hs1 : 4 ∣ s - 2:= by exact Int.dvd_sub_of_emod_eq hs1
          rcases hs1 with ⟨b, hb⟩
          replace hb : s = 2 * (2 * b + 1):= by omega
          rw [hb] at hk
          rw [show 2 * (2 * b + 1) * (5 ^ 2 ^ (n + 1) - 3 ^ 2 ^ (n + 1)) = 2 * ((2 * b + 1) * (5 ^ 2 ^ (n + 1) - 3 ^ 2 ^ (n + 1))) by ring_nf] at hk
          have g1 : (2 : ℤ) ≠ 0:= by omega
          replace hk : 2 ^ k ∣ ((2 * b + 1) * (5 ^ 2 ^ (n + 1) - 3 ^ 2 ^ (n + 1))):= by exact Int.dvd_of_mul_dvd_mul_left g1 hk
          clear g1
          -- 2 and (2*b + 1) are coprime
          have g2 : IsCoprime 2 (2 * b + 1):= by refine IsCoprime.mul_add_left_right (by exact Int.isCoprime_iff_gcd_eq_one.mpr rfl) b
          replace g2 : IsCoprime (2 ^ k) (2 * b + 1):= by exact IsCoprime.pow_left g2
          replace hk : (2 : ℤ) ^ k ∣ 5 ^ 2 ^ (n + 1) - 3 ^ 2 ^ (n + 1):= by exact IsCoprime.dvd_of_dvd_mul_left g2 hk
          -- Use the fact that 5^{2^{n+1}} - 3^{2^{n+1}} = 2 * a_{2^{n+1}-1}
          have g3:= h3 (2 ^ (n + 1) - 1)
          replace g1 : 2 ^ (n + 1) > 0:= by positivity
          rw [show 2 ^ (n + 1) - 1 + 1 = 2 ^ (n + 1) by omega] at g3
          rw [←g3] at hk
          by_cases hk1 : k = 0
          -- If k = 0, then the bound is trivial
          .
            subst k
            simp
          -- If k > 0, use the inductive hypothesis
          .
            set k1:= k - 1 with hk1
            clear_value k1
            replace hk1 : k = k1 + 1:= by omega
            subst k
            rw [show (2 : ℤ) ^ (k1 + 1) = 2 * 2 ^ k1 by ring_nf] at hk
            have g4 : (2 : ℤ) ≠ 0:= by omega
            replace hk : 2 ^ k1 ∣ a (2 ^ (n + 1) - 1):= by exact Int.dvd_of_mul_dvd_mul_left g4 hk
            -- Apply the inductive hypothesis
            specialize ih2 hk
            linarith
    -- Apply the general result for n = 2018 to get the desired result
    specialize h4 (t - 1)
    rw [show t - 1 + 1 = 2019 by omega] at h4
    rw [show t - 1 + 3 = 2021 by omega] at h4
    subst t
    exact h4
