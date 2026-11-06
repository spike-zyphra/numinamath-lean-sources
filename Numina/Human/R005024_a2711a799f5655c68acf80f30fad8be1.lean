import Mathlib

/- Find all pairs $(m, n)$ of positive integers such that

$$
125 \cdot 2^{n}-3^{m}=271
$$ -/
theorem number_theory_605112 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ (125 * 2 ^ n - 3 ^ m : ℤ) = 271} = {(6, 3)} := by
  -- Break the goal into two parts.
  ext ⟨m, n⟩
  simp
  apply Iff.intro
  . -- First show that the condition implies that (m, n) = (6, 3).
    rintro ⟨h₀, h₁, h₂⟩
    -- Examine the equation modulo 5 to get 3 ^ (m + 2) ≡ 1 (mod 5).
    have h₃ : 3 ^ (m + 2) ≡ 1 [ZMOD (5 : ℕ)] := by
      symm
      apply eq_add_of_sub_eq at h₂
      replace h₂ := congr_arg (· * 3 ^ 2) h₂
      simp only at h₂
      rw [add_mul, <-pow_add] at h₂
      simp at h₂
      rw [Int.modEq_iff_dvd]
      simp
      rw [<-Int.dvd_add_left (show 5 ∣ 2440 by norm_num), sub_add_comm]
      simp [<-h₂]
      calc
        _ ∣ (125 : ℤ) := by norm_num
        _ ∣ 125 * 2 ^ n * 9 := by
          rw [mul_assoc]
          apply Int.dvd_mul_right
    -- Get m ≡ 2 (mod 4) from the above.
    replace h₃ : m + 2 ≡ 0 [MOD 4] := by
      rw [<-ZMod.intCast_eq_intCast_iff] at h₃
      push_cast at h₃
      rw [pow_eq_one_iff_modEq] at h₃
      suffices orderOf (3 : ZMod 5) = 4 by
        simp [this] at h₃
        exact h₃
      -- Prove that orderOf (3 : ZMod 5) = 4.
      apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by norm_cast)
      -- For any prime that divides 4, 3 ^ (4 / p) does not equal 1 modulo 5.
      intro p hp hp'
      rw [show 4 = 2 ^ 2 by norm_num] at hp'
      apply Prime.dvd_of_dvd_pow (Nat.prime_iff.mp hp) at hp'
      rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_two)] at hp'
      simp [hp']
      norm_cast
    -- Get m = 4k + 2 for some k.
    rw [Nat.modEq_zero_iff_dvd, dvd_iff_exists_eq_mul_right] at h₃
    obtain ⟨k', h₃⟩ := h₃
    have h₄ : 1 ≤ k' := by
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₄
    replace h₃ : m = 2 * (2 * k + 1) := by
      omega
    clear h₄
    -- Substitute m = 4k + 2 into the original equation.
    rw [h₃, pow_mul] at h₂
    -- Examine the equation modulo 7 to get (2 ^ n % 7 + 2 ^ (2k + 1) % 7) % 7 = 2.
    have h₄ : (2 ^ n % 7 + 2 ^ (2 * k + 1) % 7) % 7 = 2 % 7 := by
      apply eq_add_of_sub_eq at h₂
      replace h₂ := congr_arg (· % 7) h₂
      simp at h₂
      norm_cast at h₂
      simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at h₂
      norm_num at h₂
      rw [<-Nat.add_mod]
      symm
      rw [<-Nat.ModEq.eq_1, Nat.modEq_iff_dvd] at h₂ ⊢
      rw [<-@Int.dvd_add_left _ _ (7 - 7 * 2 ^ n)]
      zify at h₂ ⊢
      convert h₂ using 1
      . ring
      . omega
    -- Note that 2 ^ s % 7 = 1, 2 or 4 for s ≡ 0, 1 or 2 (mod 3).
    have h₅ (s : ℕ) : 2 ^ s ≡ 2 ^ (s % 3) [ZMOD (7 : ℕ)] := by
      rw [<-ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [<-pow_mod_orderOf]
      suffices orderOf (2 : ZMod 7) = 3 by
        rw [this]
      -- Show that orderOf (2 : ZMod 7) = 3.
      apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by norm_cast)
      -- For any prime that divides 3, 2 ^ (3 / p) does not equal 1 modulo 7.
      intro p hp hp'
      rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_three)] at hp'
      simp [hp']
      norm_cast
    -- We get n % 3 = 0 and (2k + 1) % 3 = 0 by listing all possibilities.
    have h₆ : n % 3 = 0 ∧ (2 * k + 1) % 3 = 0 := by
      have h3mod (s : ℕ) : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by
        omega
      rcases h3mod n with (g₀ | g₀ | g₀)
      all_goals
        rcases h3mod (2 * k + 1) with (g₁ | g₁ | g₁)
        all_goals
          have g₂ := h₅ n
          have g₃ := h₅ (2 * k + 1)
          simp [g₀, g₁, Int.ModEq.eq_1] at g₂ g₃
          zify at h₄
          simp [g₂, g₃] at h₄
          try tauto
    clear h₅
    obtain ⟨h₅, h₆⟩ := h₆
    -- We get 3 ∣ n and 3 ∣ m.
    rw [<-Nat.dvd_iff_mod_eq_zero] at h₅ h₆
    replace h₆ : 3 ∣ m := by
      calc
        _ ∣ 2 * k + 1 := h₆
        _ ∣ m := by
          rw [h₃]
          apply Nat.dvd_mul_left
    -- Let n = 3x and m = 3y.
    rw [dvd_iff_exists_eq_mul_right] at h₅ h₆
    obtain ⟨x, h₅⟩ := h₅
    obtain ⟨y, h₆⟩ := h₆
    -- Change the original equation to (5 * 2 ^ x) ^ 3 - (3 ^ y) ^ 3 = 271.
    rw [<-pow_mul, <-h₃, h₅, h₆, mul_comm 3, mul_comm 3, pow_mul, pow_mul, show (125 : ℤ) = 5 ^ 3 by norm_num, <-mul_pow] at h₂
    -- Factorize to get (5 * 2 ^ x) ^ 2 + (5 * 2 ^ x) * (3 ^ y) + (3 ^ y) ^ 2 ≤ 271.
    have h₃ := h₂
    rw [show (5 * 2 ^ x : ℤ) ^ 3 - (3 ^ y) ^ 3 = ((5 * 2 ^ x) - (3 ^ y)) * ((5 * 2 ^ x) ^ 2 + (5 * 2 ^ x) * (3 ^ y) + (3 ^ y) ^ 2) by ring] at h₃
    replace h₃ : (5 * 2 ^ x : ℤ) ^ 2 + (5 * 2 ^ x) * (3 ^ y) + (3 ^ y) ^ 2 ≤ 271 := by
      -- We are using the fact that (5 * 2 ^ x) ^ 2 + (5 * 2 ^ x) * (3 ^ y) + (3 ^ y) ^ 2 > 0, so 5 * 2 ^ x - 3 * y > 0, hence the expression h₂ is a product of two natural number.
      nlinarith [show (5 * 2 ^ x : ℤ) - (3 ^ y) > 0 by by_contra!; nlinarith [show (5 * 2 ^ x : ℤ) ^ 2 + (5 * 2 ^ x) * (3 ^ y) + (3 ^ y) ^ 2 > 0 by positivity]]
    -- Therefore, 5 * 2 ^ x < 20, so x < 2.
    replace h₃ : 5 * 2 ^ x < 5 * 2 ^ 2 := by
      simp
      rw [<-sq_lt_sq₀ (by positivity) (by norm_num)]
      zify
      linarith [show (5 * 2 ^ x : ℤ) * (3 ^ y) + (3 ^ y) ^ 2 > 0 by positivity]
    rw [Nat.mul_lt_mul_left (by norm_num), Nat.pow_lt_pow_iff_right (by norm_num)] at h₃
    replace h₃ : x = 1 := by
      omega
    -- Substitute x = 1 into h₂ to get y = 2.
    replace h₂ : (3 ^ y) ^ 3 = (3 ^ 2) ^ 3 := by
      norm_num [h₃] at h₂
      linarith only [h₂]
    apply Nat.pow_left_injective (by norm_num) at h₂
    apply Nat.pow_right_injective (by norm_num) at h₂
    -- We get (m, n) = (3 * 1, 3 * 2) = (3, 6)
    omega
  . -- Show that (m, n) = (3, 6) does satisfy the given condition.
    rintro ⟨h₀, h₁⟩
    subst m n
    norm_num