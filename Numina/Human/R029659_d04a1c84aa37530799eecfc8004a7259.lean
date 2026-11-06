import Mathlib
/- Define the Fibonacci numbers by $F_{0}=0, F_{1}=1, F_{n}=F_{n-1}+F_{n-2}$ for $n \geq 2$. For how many $n, 0 \leq n \leq 100$, is $F_{n}$ a multiple of 13 ? -/
theorem algebra_611144 (F : ℕ → ℕ) (h0 : F 0 = 0) (h1 : F 1 = 1) (h : ∀ n : ℕ, F (n + 2) = F (n + 1) + F n) : {n : ℕ | n ≤ 100 ∧ F n ≡ 0 [ZMOD 13]}.ncard = 15:= by
  -- Prove that F(n+7) ≡ 8*F(n) (mod 13)
  have h2 : ∀ n : ℕ, F (n + 7) ≡ 8 * F n [ZMOD 13] := by
    intro n
    rw [h (n + 5), h (n + 4), h (n + 3), h (n + 2), h (n + 1), h n]
    ring_nf
    have g1 : 13 ≡ 0 [ZMOD 13]:= by rfl
    replace g1 : F (1 + n) * 13 ≡ F (1 + n) * 0 [ZMOD 13]:= by exact Int.ModEq.mul_left (F (1 + n)) g1
    simp at g1
    have g2 : F n * 8 ≡ F n * 8 [ZMOD 13]:= by exact rfl
    replace g1 : F (1 + n) * 13 + F n * 8 ≡ 0 + F n * 8 [ZMOD 13]:= by exact Int.ModEq.add g1 g2
    simp at g1
    exact g1

  -- Generalize the pattern: F(n+7k) ≡ 8^k * F(n) (mod 13)
  have h3 : ∀ k n : ℕ, F (n + 7 * k) ≡ 8 ^ k * F n [ZMOD 13] := by
    intro k
    induction k with
    | zero =>
      intro n
      simp
    | succ k ih =>
      intro n
      specialize h2 (n + 7 * k)
      ring_nf at h2
      ring_nf
      specialize ih n
      replace ih : F (n + 7 * k) * 8 ≡ 8 ^ k * F n * 8 [ZMOD 13]:= by exact Int.ModEq.mul ih rfl
      ring_nf at ih
      exact Int.ModEq.trans h2 ih

  -- Prove that F(1) is not divisible by 13
  have t1 : ¬(13 ∣ F 1):= by
    rw [h1]
    simp

  -- Prove that F(2) is not divisible by 13
  have t2 : ¬(13 ∣ F 2):= by
    rw [h 0]
    simp
    rw [h0, h1]
    simp

  -- Prove that F(3) is not divisible by 13
  have t3 : ¬(13 ∣ F 3):= by
    rw [h 1, h 0]
    simp
    rw [h0, h1]
    simp
    omega

  -- Prove that F(4) is not divisible by 13
  have t4 : ¬(13 ∣ F 4):= by
    rw [h 2, h 1, h 0]
    simp
    rw [h0, h1]
    simp
    omega

  -- Prove that F(5) is not divisible by 13
  have t5 : ¬(13 ∣ F 5):= by
    rw [h 3, h 2, h 1, h 0]
    simp
    rw [h0, h1]
    simp
    omega

  -- Prove that F(6) is not divisible by 13
  have t6 : ¬(13 ∣ F 6):= by
    rw [h 4, h 3, h 2, h 1, h 0]
    simp
    rw [h0, h1]
    simp
    omega

  -- Key insight: F(n) is divisible by 13 if and only if 7 divides n
  replace h3 : ∀ n : ℕ, F n ≡ 0 [ZMOD 13] ↔ 7 ∣ n:= by
    intro n
    constructor
    .
      intro h
      set r:= n % 7 with hr
      set q:= n / 7 with hq
      clear_value r q
      have g1 : n = 7 * q + r:= by
        rw [hr, hq]
        exact Eq.symm (Nat.div_add_mod n 7)
      have g2 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6:= by
        rw [hr]
        omega
      rcases g2 with g2 | g2 | g2 | g2 | g2 | g2 | g2
      .
        subst r
        replace g2 : 7 ∣ n:= by exact Nat.dvd_of_mod_eq_zero g2
        exact g2
      all_goals
        replace g1 : ∃ k : ℕ, n = 7 * k + r:= by exact Exists.intro q g1
        rcases g1 with ⟨k, hk⟩
        by_contra _
        specialize h3 k r
        ring_nf at hk h3
        rw [←hk] at h3
        replace h3 : F r * 8 ^ k ≡ 0 [ZMOD 13]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h)) h3)
        replace h3 : 13 ∣  F r * (8 : ℤ) ^ k:= by exact Int.dvd_of_emod_eq_zero h3
        replace h3 : 13 ∣ F r * 8 ^ k:= by
          zify
          exact h3
        have g1 : Nat.Prime 13:= by decide
        replace h3 : 13 ∣ F r ∨ 13 ∣ 8 ^ k:= by exact (Nat.Prime.dvd_mul g1).mp h3
        rcases h3 with h3 | h3
        .
          rw [g2] at h3
          trivial
        .
          replace h3 : 13 ∣ 8:= by exact Nat.Prime.dvd_of_dvd_pow g1 h3
          omega
    .
      intro h
      replace h : ∃ k : ℕ, n = 7 * k:= by exact h
      rcases h with ⟨k, hk⟩
      subst n
      specialize h3 k 0
      simp at h3
      rw [h0] at h3
      simp at h3
      exact h3

  -- Clean up temporary variables
  clear t1 t2 t3 t4 t5 t6

  -- Identify the exact set of n ≤ 100 where F(n) is divisible by 13
  have h4 : {n | n ≤ 100 ∧ ↑(F n) ≡ 0 [ZMOD 13]} = {0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98}:= by
    ext n
    constructor
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      replace h3:= (h3 n).1 h2
      replace h3 : ∃ k : ℕ, n = 7 * k:= by exact h3
      rcases h3 with ⟨k, hk⟩
      subst n
      replace h1 : k ≤ 14:= by omega
      simp
      omega
    .
      intro h
      simp
      constructor
      .
        simp at h
        omega
      .
        suffices 7 ∣ n by exact (h3 n).2 this
        simp at h
        rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        all_goals
          subst n
          omega

  -- Calculate the cardinality of the set to prove there are exactly 15 such numbers
  rw [h4]
  rw [show ({0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98} : Set ℕ) = ({0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98} : Finset ℕ) by simp]
  rw [Set.ncard_coe_Finset]
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  all_goals
    simp
