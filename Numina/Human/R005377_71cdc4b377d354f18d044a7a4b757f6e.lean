import Mathlib

/- Find all triples of integers $(x, y, z)$ satisfying

$$
x^{3}+y^{3}+z^{3}-3 x y z=2003
$$ -/
theorem algebra_607981 :
    {(x, y, z) : ℤ × ℤ × ℤ | x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z = 2003} = {(667, 668, 668), (668, 667, 668), (668, 668, 667)} := by
  -- Simplify the goal into two parts.
  ext ⟨x, y, z⟩
  apply Iff.intro
  . -- First show that the equation implies the three solutions.
    intro h₀
    simp at h₀ ⊢
    -- Use the fact that x³ + y³ + z³ - 3xyz = (x + y + z)(((x - y)² + (y - z)² + (z - x)²) / 2).
    have h₁ : (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) = 4006 := by
      linarith only [h₀]
    -- Show that x + y + z ≥ 0 (because it is non-negative after multiplied by a sum of squares).
    have h₂ : x + y + z ≥ 0 := by
      nlinarith
    -- Note that 4006 = 2 * 2003 and 2003 is a prime number, so it is only possible that x + y + z = 2 and (x - y)² + (y - z)² + (z - x)² = 2003, or x + y + z = 2003 and (x - y)² + (y - z)² + (z - x)² = 2.
    let s := ((x + y + z).natAbs, ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2).natAbs)
    have hs : s = (1, 4006) ∨ s = (2, 2003) ∨ s = (2003, 2) ∨ s = (4006, 1) := by
      have hfactor : s.1 * s.2 = 4006 ∧ 4006 ≠ 0 := by
        simp [s]
        rw [<-Int.natAbs_mul, h₁]
        norm_num
      rw [<-Nat.mem_divisorsAntidiagonal] at hfactor
      -- Use the computer to find the factors of 4006 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 4006 = {(1, 4006), (2, 2003), (2003, 2), (4006, 1)} by native_decide] at hfactor
      simp at hfactor
      exact hfactor
    -- Note that 2 ∣ ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2), so two possibilities are eliminated.
    have hs' : 2 ∣ ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by
      rw [dvd_iff_exists_eq_mul_right]
      use (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x)
      ring
    -- Eliminate the two possibilities that (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 is odd.
    obtain hs | hs | hs | hs := hs
    . -- Suppose that (x + y + z, (x - y)² + (y - z)² + (z - x)²) = (1, 4006).
      clear hs'
      simp [s] at hs
      have h₃ := congr_arg (· % 3) hs.2
      simp at h₃
      iterate 2 rw [Int.natAbs_add_of_nonneg (by positivity) (by positivity)] at h₃
      nth_rw 1 [<-Int.natAbs_sq] at h₃
      nth_rw 2 [<-Int.natAbs_sq] at h₃
      nth_rw 3 [<-Int.natAbs_sq] at h₃
      zify at hs
      iterate 2 rw [abs_of_nonneg (by positivity)] at hs
      -- A small lemma that the square of an integer is either 0 or 1 modulo 3.
      have square_mod_3 (a : ℕ) : a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
        have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
          omega
        rcases this with (h | h | h)
        <;> simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
      -- Since the squares add up to remainder 1 modulo 3, there must be two squares that are 0 modulo 3 and one square that is 1 modulo 3.
      have sum_of_three_mod_3 (a b c : ℕ) (ha : a % 3 = 0 ∨ a % 3 = 1) (hb : b % 3 = 0 ∨ b % 3 = 1) (hc : c % 3 = 0 ∨ c % 3 = 1) (h : (a + b + c) % 3 = 1) :
          (a % 3 = 0 ∧ b % 3 = 0 ∧ c % 3 = 1) ∨ (a % 3 = 0 ∧ b % 3 = 1 ∧ c % 3 = 0) ∨ (a % 3 = 1 ∧ b % 3 = 0 ∧ c % 3 = 0) := by
        rcases ha with (ha | ha)
        <;> rcases hb with (hb | hb)
          <;> rcases hc with (hc | hc)
            <;> simp [ha, hb, hc, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at h ⊢
            <;> omega
      -- Apply the two lemmas above.
      have : ((x - y).natAbs ^ 2 % 3 = 0 ∧ (y - z).natAbs ^ 2 % 3 = 0 ∧ (z - x).natAbs ^ 2 % 3 = 1) ∨ ((x - y).natAbs ^ 2 % 3 = 0 ∧ (y - z).natAbs ^ 2 % 3 = 1 ∧ (z - x).natAbs ^ 2 % 3 = 0) ∨ ((x - y).natAbs ^ 2 % 3 = 1 ∧ (y - z).natAbs ^ 2 % 3 = 0 ∧ (z - x).natAbs ^ 2 % 3 = 0) := by
        have h1 := square_mod_3 (x - y).natAbs
        have h2 := square_mod_3 (y - z).natAbs
        have h3 := square_mod_3 (z - x).natAbs
        exact sum_of_three_mod_3 _ _ _ h1 h2 h3 h₃
      clear square_mod_3 sum_of_three_mod_3
      -- Since (x - y)² + (y - z)² + (z - x)² ≡ 1 (MOD 3), there must be two terms that is divisible by 3 and one term that is not, which is impossible.
      obtain this | this | this := this
      . -- Suppose (x - y)² % 3 = 0, (y - z)² % 3 = 0, (z - x)² % 3 = 1.
        iterate 2 rw [<-Nat.dvd_iff_mod_eq_zero] at this
        zify at this
        iterate 3 rw [sq_abs] at this
        -- Show that 3 ∣ x - y.
        have g₀ := Int.Prime.dvd_pow (Nat.prime_three) this.1
        -- Show that 3 ∣ y - z.
        have g₁ := Int.Prime.dvd_pow (Nat.prime_three) this.2.1
        zify at g₀ g₁
        simp at g₀ g₁
        -- Show that 3 ∣ x - z.
        have g₂ : 3 ∣ x - z := by
          rw [show x - z = (x - y) + (y - z) by ring]
          apply dvd_add g₀ g₁
        -- A contradiction is derived.
        omega
      . -- Suppose (x - y)² % 3 = 0, (y - z)² % 3 = 1, (z - x)² % 3 = 0.
        iterate 2 rw [<-Nat.dvd_iff_mod_eq_zero] at this
        zify at this
        iterate 3 rw [sq_abs] at this
        -- Show that 3 ∣ x - y.
        have g₀ := Int.Prime.dvd_pow (Nat.prime_three) this.1
        -- Show that 3 ∣ z - x
        have g₂ := Int.Prime.dvd_pow (Nat.prime_three) this.2.2
        zify at g₀ g₂
        simp at g₀ g₂
        -- Show that 3 ∣ y - z.
        have g₁ : 3 ∣ y - z := by
          rw [show y - z = -(z - y) by ring, dvd_neg]
          rw [show z - y = (x - y) + (z - x) by ring]
          apply dvd_add g₀ g₂
        -- A contradiction is derived.
        omega
      . -- Suppose (x - y)² % 3 = 1, (y - z)² % 3 = 0, (z - x)² % 3 = 0.
        iterate 2 rw [<-Nat.dvd_iff_mod_eq_zero] at this
        zify at this
        iterate 3 rw [sq_abs] at this
        -- Show that 3 ∣ y - z.
        have g₁ := Int.Prime.dvd_pow (Nat.prime_three) this.2.1
        -- Show that 3 ∣ z - x.
        have g₂ := Int.Prime.dvd_pow (Nat.prime_three) this.2.2
        zify at g₁ g₂
        simp at g₁ g₂
        -- Show that 3 ∣ x - y.
        have g₀ : 3 ∣ x - y := by
          rw [show x - y = -(y - x) by ring, dvd_neg]
          rw [show y - x = (y - z) + (z - x) by ring]
          apply dvd_add g₁ g₂
        -- A contradiction is derived.
        omega
    . -- It is impossible that (x + y + z, (x - y)² + (y - z)² + (z - x)²) = (2, 2003).
      simp [s] at hs
      zify at hs
      iterate 2 rw [abs_of_nonneg (by positivity)] at hs
      rw [hs.2] at hs'
      omega
    . -- Suppose that (x + y + z, (x - y)² + (y - z)² + (z - x)²) = (2003, 2).
      clear hs'
      simp [s] at hs
      have h₃ := congr_arg (· % 3) hs.2
      simp at h₃
      iterate 2 rw [Int.natAbs_add_of_nonneg (by positivity) (by positivity)] at h₃
      nth_rw 1 [<-Int.natAbs_sq] at h₃
      nth_rw 2 [<-Int.natAbs_sq] at h₃
      nth_rw 3 [<-Int.natAbs_sq] at h₃
      zify at hs
      iterate 2 rw [abs_of_nonneg (by positivity)] at hs
      -- A small lemma that the square of an integer is either 0 or 1 modulo 3.
      have square_mod_3 (a : ℕ) : a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
        have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
          omega
        rcases this with (h | h | h)
        <;> simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
      -- Since the squares add up to remainder 2 modulo 3, there must be two squares that are 1 modulo 3 and one square that is 0 modulo 3.
      have sum_of_three_mod_3 (a b c : ℕ) (ha : a % 3 = 0 ∨ a % 3 = 1) (hb : b % 3 = 0 ∨ b % 3 = 1) (hc : c % 3 = 0 ∨ c % 3 = 1) (h : (a + b + c) % 3 = 2) :
          (a % 3 = 1 ∧ b % 3 = 1 ∧ c % 3 = 0) ∨ (a % 3 = 1 ∧ b % 3 = 0 ∧ c % 3 = 1) ∨ (a % 3 = 0 ∧ b % 3 = 1 ∧ c % 3 = 1) := by
        rcases ha with (ha | ha)
        <;> rcases hb with (hb | hb)
          <;> rcases hc with (hc | hc)
            <;> simp [ha, hb, hc, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at h ⊢
            <;> omega
      -- Apply the two lemmas above.
      have : ((x - y).natAbs ^ 2 % 3 = 1 ∧ (y - z).natAbs ^ 2 % 3 = 1 ∧ (z - x).natAbs ^ 2 % 3 = 0) ∨ ((x - y).natAbs ^ 2 % 3 = 1 ∧ (y - z).natAbs ^ 2 % 3 = 0 ∧ (z - x).natAbs ^ 2 % 3 = 1) ∨ ((x - y).natAbs ^ 2 % 3 = 0 ∧ (y - z).natAbs ^ 2 % 3 = 1 ∧ (z - x).natAbs ^ 2 % 3 = 1) := by
        have h1 := square_mod_3 (x - y).natAbs
        have h2 := square_mod_3 (y - z).natAbs
        have h3 := square_mod_3 (z - x).natAbs
        exact sum_of_three_mod_3 _ _ _ h1 h2 h3 h₃
      clear square_mod_3 sum_of_three_mod_3
      -- Since (x - y)² + (y - z)² + (z - x)² = 2, there must be two terms that equals one and one term that equals zero.
      obtain this | this | this := this
      . -- Suppose (x - y)² % 3 = 1, (y - z)² % 3 = 1, (z - x)² % 3 = 0.
        have g₀ : (x - y).natAbs ^ 2 ≥ 1 := by
          omega
        have g₁ : (y - z).natAbs ^ 2 ≥ 1 := by
          omega
        zify at g₀ g₁
        rw [sq_abs] at g₀ g₁
        have g₂ : (z - x) ^ 2 = 0 := by
          linarith only [g₀, g₁, hs.2, sq_nonneg (z - x)]
        simp at g₂
        -- Show that x = z and substitute into other hypotheses.
        replace g₂ : x = z := by
          linarith only [g₂]
        rw [<-g₂] at hs
        have g₃ : (x - y) ^ 2 = 1 := by
          linarith only [hs.2]
        -- Now x - y = ±1.
        simp at g₃
        omega
      . -- Suppose (x - y)² % 3 = 0, (y - z)² % 3 = 0, (z - x)² % 3 = 1.
        have g₀ : (x - y).natAbs ^ 2 ≥ 1 := by
          omega
        have g₂ : (z - x).natAbs ^ 2 ≥ 1 := by
          omega
        zify at g₀ g₂
        rw [sq_abs] at g₀ g₂
        have g₁ : (y - z) ^ 2 = 0 := by
          linarith only [g₀, g₂, hs.2, sq_nonneg (y - z)]
        simp at g₁
        -- Show that y = z and substitute into other hypotheses.
        replace g₁ : y = z := by
          linarith only [g₁]
        rw [<-g₁] at hs
        have g₃ : (x - y) ^ 2 = 1 := by
          linarith only [hs.2]
        -- Now x - y = ±1.
        simp at g₃
        omega
      . -- Suppose (x - y)² % 3 = 0, (y - z)² % 3 = 1, (z - x)² % 3 = 1.
        have g₁ : (y - z).natAbs ^ 2 ≥ 1 := by
          omega
        have g₂ : (z - x).natAbs ^ 2 ≥ 1 := by
          omega
        zify at g₁ g₂
        rw [sq_abs] at g₁ g₂
        have g₀ : (x - y) ^ 2 = 0 := by
          linarith only [g₁, g₂, hs.2, sq_nonneg (x - y)]
        simp at g₀
        -- Show that x = y and substitute into other hypotheses.
        replace g₀ : x = y := by
          linarith only [g₀]
        rw [<-g₀] at hs
        have g₃ : (x - z) ^ 2 = 1 := by
          linarith only [hs.2]
        -- Now x - z = ±1.
        simp at g₃
        omega
    . -- It is impossible that (x + y + z, (x - y)² + (y - z)² + (z - x)²) = (4006, 1).
      simp [s] at hs
      zify at hs
      iterate 2 rw [abs_of_nonneg (by positivity)] at hs
      rw [hs.2] at hs'
      omega
  . -- Show that the three numbers indeed satisfy the equation.
    intro h
    simp at h ⊢
    obtain h | h | h := h
    all_goals
      rw [h.1, h.2.1, h.2.2]
      norm_num