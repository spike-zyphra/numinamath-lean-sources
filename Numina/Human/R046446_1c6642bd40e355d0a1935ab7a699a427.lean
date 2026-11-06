import Mathlib

/- Let $n$ be the least positive integer for which $149^n-2^n$ is divisible by $3^3\cdot5^5\cdot7^7.$ Find the number of positive integer divisors of $n.$ -/
theorem number_theory_98068 {n : ℕ} :
    IsLeast {x | 0 < x ∧ (3^3 * 5^5 * 7^7) ∣ (149^x - 2^x)} n →
    (n.divisors.card = 270) := by
  set s := {x | _}
  -- it is enough to show that n = 2 ^ 2 * 3 ^ 2 * 5 ^ 4 * 7 ^ 5
  suffices hn : IsLeast s (2 ^ 2 * 3 ^ 2 * 5 ^ 4 * 7 ^ 5) by
    intro h
    rw [IsLeast.unique h hn]
    -- 2 ^ 2 * 3 ^ 2 * 5 ^ 4 * 7 ^ 5 has 270 divisors
    -- this result follows from properties of the arithmetic function σ₀
    repeat rw [Nat.Coprime.card_divisors_mul (by norm_num)]
    simp_rw [←ArithmeticFunction.sigma_zero_apply]
    repeat rw [ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num)]
  -- let v_p(x) be the multiplicity of p in x
  -- 3 ^ 3 * 5 ^ 5 * 7 ^ 7 divdes x iff 3 ≤ v_3(x), 5 ≤ v_5(x), and 7 ≤ v_7(x)
  have h_dvd (n : ℕ) : 3^3 * 5^5 * 7^7 ∣ n ↔ 3 ≤ emultiplicity 3 n ∧ 5 ≤ emultiplicity 5 n ∧ 7 ≤ emultiplicity 7 n := by
    have h {a b c : ℕ} (h : a.Coprime b) : a * b ∣ c ↔ a ∣ c ∧ b ∣ c := by
      constructor
      · exact fun ⟨k, h⟩ => ⟨⟨b * k, by linarith⟩, ⟨a * k, by linarith⟩⟩
      · exact fun ⟨ha, hb⟩ => Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb
    rw [h (by norm_num), h (by norm_num)]
    simp_rw [pow_dvd_iff_le_emultiplicity, and_assoc]
    norm_cast
  simp_rw [s, h_dvd]
  -- apply the lifting the exponent lemma (LTE) to v_3(149 ^ n - 2 ^ n) and get
  -- v_3(149 ^ n - 2 ^ n) = v_3(149 - 2) + v_3(n)
  simp_rw [Nat.emultiplicity_pow_sub_pow Nat.prime_three (by decide) (show 3 ∣ 149 - 2 by norm_num) (by norm_num)]
  -- apply LTE to v_7(149 ^ n - 2 ^ n) and get
  -- v_7(149 ^ n - 2 ^ n) = v_7(149 - 2) + v_7(n)
  simp_rw [Nat.emultiplicity_pow_sub_pow (by norm_num) (by decide) (show 7 ∣ 149 - 2 by norm_num) (by norm_num)]
  -- we cannot apply LTE to v_5(149 ^ n - 2 ^ n) directly because 5 does not divide 149 - 2
  -- prove the following result:
  -- if 5 divides 149 ^ n - 2 ^ n then n is a multiple of 4 (n = 4 * k) and
  -- v_5(149 ^ n - 2 ^ n) = v_5(149 ^ 4 - 2 ^ 4) + v_5(k)
  have h5_imp (n : ℕ) (hm : 5 ∣ (149 ^ n - 2 ^ n)) :
      ∃ k, n = 4 * k ∧ emultiplicity 5 (149 ^ n - 2 ^ n) = emultiplicity 5 (149 ^ 4 - 16) + emultiplicity 5 k := by
    -- it is enough to show that 4 divides n
    suffices h : 4 ∣ n by
      have ⟨k, hk⟩ := h
      use k, hk
      simp_rw [hk, pow_mul]
      -- if n = 4 * k for some k then
      -- v_5(149 ^ n - 2 ^ n) = v_5(149 ^ 4 ^ k - 2 ^ 4 ^ k) = v_5(149 ^ 4 - 2 ^ 4) + v_5(k)
      -- (we can apply LTE to v_5(149 ^ 4 ^ k - 2 ^ 4 ^ k) because 5 divides 149 ^ 4 - 2 ^ 4)
      rw [Nat.emultiplicity_pow_sub_pow Nat.prime_five (by decide) (by norm_num) (by norm_num)]
      norm_num
    have p5 : Fact ((5).Prime) := ⟨Nat.prime_five⟩
    -- 4 is the order of 2 (mod 5)
    have h_order : orderOf (2 : ZMod 5) = 4 := by
      rw [orderOf_eq_iff (by norm_num)]
      reduce_mod_char
      refine ⟨trivial, ?_⟩
      intro m hm1 hm2
      interval_cases m <;> reduce_mod_char <;> decide
    -- 4 = order of 2 (mod 5) divides n iff 2 ^ n = 1 (mod 5)
    rw [← h_order, orderOf_dvd_iff_pow_eq_one]
    -- we have that 5 divides 149 ^ n - 2 ^ n
    -- we get 4 ^ n = 2 ^ n (mod 5), or 2 ^ n * (2 ^ n + 4) = 0 (mod 5)
    zify [show 2 ^ n ≤ 149 ^ n from Nat.pow_le_pow_of_le_left (by norm_num) n] at hm
    rw [show (5 : ℤ) = (5 : ℕ) from rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
    rw [← sub_eq_zero]
    push_cast at hm
    reduce_mod_char at hm ⊢
    have eq : (2 : ZMod 5) ^ n * (2 ^ n + 4) = 0 := by
      ring_nf
      rw [add_comm, mul_comm, pow_mul]
      linear_combination hm
    -- 2 ^ n ≠ 0 (mod 5) so we get 2 ^ n + 4 = 0 (mod 5)
    -- which is equivalent to 2 ^ n = 1 (mod 5)
    rw [mul_eq_zero, pow_eq_zero_iff'] at eq
    simp [show (2 : ZMod 5) ≠ 0 by exact Ne.symm (ne_of_beq_false rfl)] at eq
    exact eq
  simp only [Nat.reduceSub]
  -- compute v_5(149 ^ 4 - 2 ^ 4) = 1
  simp_rw [show emultiplicity 5 (149 ^ 4 - 16) = 1 by apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num] at h5_imp
  -- compute v_3(147) = 1
  simp_rw [show emultiplicity 3 147 = 1 by apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num]
  -- compute v_7(147) = 2
  simp_rw [show emultiplicity 7 147 = 2 by apply emultiplicity_eq_of_dvd_of_not_dvd <;> norm_num]
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, and_imp]
  have emul_eq_mul {p a b : ℕ} (hp : p ≠ 1) (ha : a ≠ 0) : emultiplicity p (a ^ b) = multiplicity p (a ^ b) := by
    rw [FiniteMultiplicity.emultiplicity_eq_multiplicity]
    rw [Nat.finiteMultiplicity_iff]
    exact ⟨hp, by positivity⟩
  -- now we need to prove several results to show that
  -- IsLeast {x | 0 < x ∧ (3^3 * 5^5 * 7^7) ∣ (149^x - 2^x)} n with
  -- n = (2 ^ 2 * 3 ^ 2 * 5 ^ 4 * 7 ^ 5)
  constructorm* _ ∧ _
  -- 0 < n is trivial
  · norm_num
  -- 3 ≤ 1 + v_3(n) follows from the properties of v_3:
  -- v_3(n) = v_3(2 ^ 2 * 3 ^ 2 * 5 ^ 4 * 7 ^ 5) = v_3(3 ^ 2) = 2
  · have p3 := Nat.prime_three.prime
    simp_rw [emultiplicity_mul p3, emultiplicity_pow_self_of_prime p3]
    repeat rw [emul_eq_mul (by norm_num) (by norm_num)]
    norm_cast
    omega
  -- show that 5 ≤ v_5(n)
  · set n := 2 ^ 2 * _ * _ * _
    -- it is enough to show that 5 divides 149 ^ n - 2 ^ n
    suffices h : 5 ∣ 149 ^ n - 2 ^ n by
      -- if 5 divides 149 ^ n - 2 ^ n then the result follows from h5_imp:
      -- v_5(149 ^ n - 2 ^ n) = 1 + v_5(n / 4) = 1 + 4 = 5 ≥ 5
      have ⟨k, hk, h5⟩ := h5_imp _ h
      have p5 : Prime 5 := Nat.prime_five.prime
      replace hk : k = 3 ^ 2 * 5 ^ 4 * 7 ^ 5 := by omega
      rw [h5, hk]
      simp_rw [emultiplicity_mul p5, emultiplicity_pow_self_of_prime p5]
      repeat rw [emul_eq_mul (by norm_num) (by norm_num)]
      norm_cast
      omega
    -- n = 4 * (3 ^ 3 * 5 ^ 4 * 7 ^ 5) = 4 * k
    have ⟨k, hk⟩ : ∃ k, n = 4 * k := by use n / 4; norm_num
    simp_rw [hk, pow_mul]
    -- 5 divides 149 ^ 4 - 2 ^ 4
    trans 149 ^ 4 - 2 ^ 4
    norm_num
    -- it follows that 5 divides 149 ^ 4 ^ k - 2 ^ 4 ^ k = 149 ^ n - 2 ^ n
    exact nat_sub_dvd_pow_sub_pow _ _ _
  -- 7 ≤ 2 + v_7(n) follows from the properties of v_7
  · have p7 : Prime 7 := Nat.Prime.prime (by norm_num)
    simp_rw [emultiplicity_mul p7, emultiplicity_pow_self_of_prime p7]
    repeat rw [emul_eq_mul (by norm_num) (by norm_num)]
    norm_cast
    omega
  -- it remains to show that 2 ^ 2 * 3 ^ 3 * 5 ^ 4 * 7 ^ 5 is minimal
  -- suppose that some number n satisfies all required properties
  -- and show that n ≤ 2 ^ 2 * 3 ^ 3 * 5 ^ 4 * 7 ^ 5
  intro n hn h3 h5 h7
  replace emul_eq_mul {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) : emultiplicity p n = multiplicity p n := by
    rw [FiniteMultiplicity.emultiplicity_eq_multiplicity]
    rw [Nat.finiteMultiplicity_iff]
    exact ⟨hp, by omega⟩
  -- show that 2 ^ 2 * 3 ^ 3 * 5 ^ 4 * 7 ^ 5 divides n
  apply Nat.le_of_dvd hn
  have h5dvd : 5 ∣ 149 ^ n - 2 ^ n := by
    apply dvd_of_emultiplicity_pos
    apply lt_of_lt_of_le _ h5
    norm_num
  -- since 5 divides 149 ^ n - 2 ^ n we get that n = 4 * k for some k (from h5_imp)
  replace ⟨k, h4, h5n⟩ := h5_imp _ h5dvd
  rw [h5n] at h5
  -- it is enough to show that 4 divides n, 3 ^ 3 divides n, 5 ^ 4 divides n,
  -- and 7 ^ 5 divides n
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
  -- n = 4 * k, so 4 divides n
  · use k, h4
  -- to show that 3 ^ 2 divides n show that 2 ≤ v_3(n)
  · apply pow_dvd_of_le_emultiplicity
    rw [emul_eq_mul (by norm_num) (by omega)] at h3 ⊢
    norm_cast at h3 ⊢
    omega
  -- to show that 5 ^ 4 divides n show that 4 ≤ v_5(n)
  · apply pow_dvd_of_le_emultiplicity
    rw [h4, emultiplicity_mul Nat.prime_five.prime]
    rw [emul_eq_mul (by norm_num) (by omega)] at h5 ⊢
    rw [emul_eq_mul (by norm_num) (by omega)]
    norm_cast at h5 ⊢
    omega
  -- to show that 7 ^ 5 divides n show that 5 ≤ v_7(n)
  · apply pow_dvd_of_le_emultiplicity
    rw [emul_eq_mul (by norm_num) (by omega)] at h7 ⊢
    norm_cast at h7 ⊢
    omega