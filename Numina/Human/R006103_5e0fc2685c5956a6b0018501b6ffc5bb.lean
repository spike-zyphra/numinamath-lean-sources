import Mathlib

/-lemma Odd.pow_injective-/
lemma Odd.pow_injective {n : ℕ} (hn : Odd n) : Function.Injective (· ^ n : ℤ → ℤ) :=
  hn.strictMono_pow.injective

/-LTE_lemma-/
lemma LTE_lemma2 (x y : ℤ) (hxy : x ≠ -y) (p n : ℕ) (hn : n > 0 ∧ Odd n)
  (hp : Nat.Prime p ∧ ¬ (p ∣ n ∨ (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y) ∧ (p : ℤ) ∣ x + y) :
  padicValInt p |x^n + y^n| = padicValInt p |x + y| := by
  -- We will reduce the sum case to a difference case by substituting y ↦ -y
  have LTE_lemma (x y : ℤ) (hxy : x ≠ y) (p n : ℕ) (hxy' : x^n ≠ y^n)
    (hp : Nat.Prime p ∧ ¬ (p ∣ n ∨ (p : ℤ) ∣ x ∨ (p : ℤ) ∣ y) ∧ (p : ℤ) ∣ (x - y)) :
    padicValInt p |x^n - y^n| = padicValInt p |x - y| := by
    -- Step 1: show that taking absolute value does not change the p-adic valuation
    have h0 (m : ℤ) : padicValInt p (abs m) = padicValInt p m := by simp [padicValInt, Int.natAbs_abs m]
    -- Step 2: use multiplicity lemma for prime p on difference of powers
    have h1 : emultiplicity (p : ℤ) (x ^ n - y ^ n) = emultiplicity (p : ℤ) (x - y) :=
      emultiplicity_pow_sub_pow_of_prime
        (Nat.prime_iff_prime_int.mp hp.1)               -- p is prime as integer
        (by tauto)                                      -- ensure p ∤ n or p ∤ x or p ∤ y
        (by tauto)                                      -- same disjunction negation
        (by norm_cast; tauto)                           -- ensure p ∣ (x - y)
    -- Guarantee p ≠ 1
    have h1' : p ≠ 1 := Nat.Prime.ne_one (by tauto)
    have hp' : Fact (p.Prime) := ⟨hp.1⟩
    -- Rewrite both sides using the `h0` lemma and the fact that padicValInt factors through multiplicity
    repeat rw [h0, padicValInt.of_ne_one_ne_zero]
    repeat rw [← Eq.symm (FiniteMultiplicity.emultiplicity_eq_multiplicity
      (padicValRat.finite_int_prime_iff.mpr (?_)))] at h1
    -- Finish with an arithmetic contradiction
    simp at h1
    all_goals omega
  -- Now apply the above lemma to x and -y to handle the sum x^n + y^n
  have hxy' : x^n ≠ (-y)^n := fun a => hxy (Odd.pow_injective hn.2 a)
  have hp' : Nat.Prime p ∧ ¬ (p ∣ n ∨ (p : ℤ) ∣ x ∨ (p : ℤ) ∣ -y)
               ∧ (p : ℤ) ∣ x - (-y) := by
    -- Repackage the original hp into the form needed for the difference lemma
    simp [hp]
  let r := LTE_lemma x (-y) hxy p n hxy' hp'
  have r1 : x^n - (-y)^n = x^n + y^n := by
    -- Since n is odd, (-y)^n = - (y^n)
    ring_nf; simp [Odd.neg_one_pow (hn.2)]
  simp [r1] at r
  exact r

/-
Let p be a prime, and a, n be positive integers. Prove that if 2^p + 3^p = a^n, then n = 1.
-/
theorem n_equal_exactly_one {a n p : ℕ} (hp : Nat.Prime p) (ha : 0 < a)
  (heq : 2^p + 3^p = a^n) : n = 1 := by
  by_cases hp_eq_2 : p = 2
  · -- Case 1: p = 2, then 2^2 + 3^2 = 13 = a^n, so n must be 1 and a = 13
    rw [hp_eq_2] at heq
    have heq1 : a = 13 ∧ n = 1 := by
      norm_num at heq
      have prime_13 : Nat.Prime 13 := by norm_num
      exact (Nat.Prime.pow_eq_iff prime_13).mp (id (Eq.symm heq))
    obtain ⟨a_val, n_val⟩ := heq1
    exact n_val

  · by_cases hp_eq_5 : p = 5
    · -- Case 2: p = 5, then 2^5 + 3^5 = 275.  Factorization arguments force n = 1.
      rw [hp_eq_5] at heq
      have heq2 : 2^5 + 3^5 = 275 := by norm_num
      rw [heq2] at heq

      -- Compute factorization of 5, 11, 25 and combine to get factorization of 275
      have hd25 : 5 * 5 = 25 := by norm_num
      have hd275 : 25 * 11 = 275 := by norm_num
      have hf5 : Nat.Prime 5 := by norm_num
      have hf11 : Nat.Prime 11 := by norm_num

      have fac5 : Nat.factorization 5 = Finsupp.single 5 1 := by exact Nat.Prime.factorization hf5
      have fac11 : Nat.factorization 11 = Finsupp.single 11 1 := by exact Nat.Prime.factorization hf11
      have fac25 : Nat.factorization 25 = Finsupp.single 5 2 := by
        calc
          Nat.factorization 25
              = Nat.factorization (5 ^ 2)       := by rfl
          _   = 2 • Nat.factorization 5         := by exact Nat.factorization_pow 5 2
          _   = 2 • Finsupp.single 5 1          := by rw [fac5]
          _   = Finsupp.single 5 2              := by simp

      -- Factorization of 275 = 25 * 11, using coprimality of 25 and 11
      have cop_25_11 : Nat.Coprime 25 11 := by decide
      have fac275 : Nat.factorization 275 = Finsupp.single 5 2 + Finsupp.single 11 1 := by
        calc
          Nat.factorization 275
              = Nat.factorization (25 * 11) := by rfl
          _   = Nat.factorization 25 + Nat.factorization 11 := by
                exact Nat.factorization_mul_of_coprime cop_25_11
          _   = Finsupp.single 5 2 + Finsupp.single 11 1 := by simp [fac25, fac11]

      -- Factorization of a^n is n • factorization a
      have fac_pow : Nat.factorization (a ^ n) = n • Nat.factorization a := by
        simp [Nat.factorization_pow a n]

      -- Compare factorization of a^n with that of 275
      have eq_f : n • Nat.factorization a = Finsupp.single 5 2 + Finsupp.single 11 1 := by
        rw [← fac_pow, ← heq]; exact fac275

      -- Focus on the coefficient of prime 11 in both sides
      have coeff_eq : (n • Nat.factorization a) 11 = (Finsupp.single 5 2 + Finsupp.single 11 1 : ℕ →₀ ℕ) 11 := by rw [eq_f]
      have rhs : (Finsupp.single 5 2 + Finsupp.single 11 1 : ℕ →₀ ℕ) 11 = 1 := by simp
      have lhs : (n • Nat.factorization a) 11 = n * (Nat.factorization a) 11 := by
        exact Finsupp.smul_apply n (Nat.factorization a) 11

      -- Conclude n * (factorization a at 11) = 1, so n = 1
      have final : n * (Nat.factorization a) 11 = 1 := by
        simp [← lhs, coeff_eq, rhs]
      exact Nat.eq_one_of_mul_eq_one_right final

    · -- Case 3: p = 3 or p ≥ 7.  We use p-adic valuation lemma to force n = 1.
      -- Ensure p ≠ 2
      have p_ne_two : p ≠ 2 := by
        intro h; have := hp_eq_2 h; contradiction
      -- Since p is prime and not 2, p must be odd
      have p_odd : p % 2 = 1 := by
        have := Nat.Prime.eq_two_or_odd hp
        cases' this with h h'
        · contradiction
        · exact h'
      -- Ensure p ≠ 5 as well
      have p_ne_five : p ≠ 5 := by intro h; contradiction
      -- Set x = 2, y = 3 in ℤ
      let x := (2 : ℤ)
      let y := (3 : ℤ)
      have hxy : x ≠ -y := by norm_num
      have prime₅ : Nat.Prime 5 := by norm_num
      have five_not_dvd_p : ¬ (5 ∣ p) := by
        intro h₁
        have hp_eq : p = 5 := by
          exact Eq.symm ((fun {p q} pp qp ↦ (Nat.prime_dvd_prime_iff_eq pp qp).mp) prime₅ hp h₁)
        exact (p_ne_five hp_eq).elim
      have five_not_dvd₂ : ¬ ((5 : ℤ) ∣ 2) := by norm_num
      have five_not_dvd₃ : ¬ ((5 : ℤ) ∣ 3) := by norm_num
      have five_dvd_sum : (5 : ℤ) ∣ (x + y) := by norm_num
      -- Combine to show 5 ∤ p, 5 ∤ x, 5 ∤ y, and 5 ∣ (x + y)
      have no_dvd_xy : ¬ ((5 : ℤ) ∣ x) ∧ ¬ ((5 : ℤ) ∣ y) := by
        exact ite_then_not_self.mp five_not_dvd₃
      have h_not_all : ¬ (5 ∣ p ∨ (5 : ℤ) ∣ x ∨ (5 : ℤ) ∣ y) := by
        push_neg; split_ands; all_goals omega
      -- Build the hypothesis for the p-adic lemma at p = 5
      have hp₅ : Nat.Prime 5 ∧ ¬ (5 ∣ p ∨ (5 : ℤ) ∣ x ∨ (5 : ℤ) ∣ y)
                     ∧ ((5 : ℤ) ∣ (x + y)) := by
        exact ⟨prime₅, h_not_all, five_dvd_sum⟩
      -- p is odd and positive
      have h_n_pos_odd : p > 0 ∧ Odd p := by
        split_ands; omega; exact Nat.odd_iff.mpr p_odd
      -- Apply the LTE_lemma2 to get p-adic valuation at 5
      have lte5 : padicValInt 5 |x^p + y^p| = padicValInt 5 |x + y| := by
        apply LTE_lemma2 x y hxy 5 p h_n_pos_odd hp₅
      -- Convert the given equality 2^p + 3^p = a^n into ℤ
      have lhs_val : padicValInt 5 |a^n| = padicValInt 5 |x^p + y^p| := by
        have heq_int : (2^p + 3^p : ℤ) = (a^n : ℤ) := by linarith
        simp; rw [heq_int]; simp
      -- Compute p-adic valuation of a^n in terms of n
      have pow_val : padicValInt 5 |(a : ℤ)^n| = n * padicValInt 5 |a| := by
        -- show a ≥ 0 in ℤ
        have nonneg_a : 0 ≤ (a : ℤ) := by exact Int.ofNat_zero_le a
        -- show a ≠ 0
        have nonzero_a : a ≠ 0 := by exact Nat.pos_iff_ne_zero.mp ha
        -- assert that 5 is prime
        have hp5fact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        simp
        calc
          padicValInt 5 ((a : ℤ) ^ n) = padicValInt 5 (↑(a ^ n)) := by simp
          _ = padicValNat 5 (a ^ n)                                := by exact rfl
          _ = n * padicValNat 5 a                                  := by
            exact padicValNat.pow n nonzero_a
      -- Combine the two valuations: n * padicValInt 5 |a| = padicValInt 5 |x + y|
      have v5_LHS : n * padicValInt 5 |a| = padicValInt 5 |x + y| := by
        omega
      -- p-adic valuation of |x + y| = |2 + 3| at 5 is 1
      have v5_sum : padicValInt 5 |x + y| = 1 := by
        norm_num
        have hp5fact : Fact (Nat.Prime 5) := ⟨by decide⟩
        exact padicValInt_self (p := 5)
      -- From n * padicValInt 5 |a| = 1, conclude n = 1
      have n_mul := by simpa [v5_sum] using v5_LHS
      exact n_mul.1
