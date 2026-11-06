import Mathlib

/- The rational numbers $x$ and $y$, when written in lowest terms, have denominators 60 and 70 , respectively. What is the smallest possible denominator of $x+y$ ?-/
theorem number_theory_611165 :
    IsLeast {n : ℤ | ∃ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ, p₁.gcd q₁ = 1 ∧ q₁ > 0 ∧ p₂.gcd q₂ = 1 ∧ q₂ > 0 ∧ q₁ = 60 ∧ q₂ = 70 ∧ q₃ > 0 ∧ (p₁ / q₁ + p₂ / q₂ : ℚ) = (p₃ / q₃ : ℚ) ∧ n = q₃} 84 := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_,?_⟩
  . -- Show that 84 is possible, because 1/60 + 3/70 = 5/84.
    use 1, 60, by norm_num, by norm_num, 3, 70
    norm_num
    use 5
    norm_num
  . -- Show that 84 is the least possible denominator.
    intro n p₁ q₁ h₀ h₁ p₂ q₂ h₂ h₃ h₄ h₅ h₆ p₃ h₇
    rw [h₄, h₅] at h₇
    -- Now simply p₁ / 60 + p₂ / 70 to (7p₁ + 6p₂) / 420.
    rw [show p₁ / (60 : ℤ) + p₂ / (70 : ℤ) = (7 * p₁ + 6 * p₂ : ℚ) / 420 by field_simp; ring] at h₇
    rw [div_eq_div_iff (by norm_num) (by simp; omega)] at h₇
    norm_cast at h₇
    -- We shall prove that 4 ∣ n.
    have h₈ : 2 ^ 2 ∣ n := by
      have h₈ : 2 ^ 2 ∣ p₃ * 420 := by
        calc
          2 ^ 2 ∣ 2 ^ 2 * (p₃ * 105) := by apply dvd_mul_right
          _ = p₃ * 420 := by ring
      rw [<-h₇] at h₈
      -- It suffices to show that 4 and (7p₁ + 6p₂) are coprime.
      apply IsCoprime.dvd_of_dvd_mul_left _ h₈
      -- It suffices to show that 2 and (7p₁ + 6p₂) are coprime.
      apply IsCoprime.pow_left
      -- It suffices to show that 2 and 7p₁ are coprime.
      rw [show 6 * p₂ = 2 * (3 * p₂) by ring]
      apply IsCoprime.add_mul_left_right
      apply IsCoprime.mul_right
      norm_num
      -- Now we shall prove that 2 and p₁ has gcd 1.
      rw [Int.isCoprime_iff_gcd_eq_one]
      rw [Int.gcd_comm, h₄] at h₀
      suffices Int.gcd 2 p₁ ∣ Int.gcd 60 p₁ by
        rw [h₀] at this
        simp_all
      rw [show (60 : ℤ) = 30 * 2 by norm_num]
      apply Int.gcd_dvd_gcd_mul_left
    -- We shall prove that 3 ∣ n.
    have h₉ : 3 ∣ n := by
      have h₉ : 3 ∣ p₃ * 420 := by
        calc
          3 ∣ 3 * (p₃ * 140) := by apply dvd_mul_right
          _ = p₃ * 420 := by ring
      rw [<-h₇] at h₉
      -- It suffices to show that 3 and (7p₁ + 6p₂) are coprime.
      apply IsCoprime.dvd_of_dvd_mul_left _ h₉
      -- It suffices to show that 3 and 7p₁ are coprime.
      rw [show 6 * p₂ = 3 * (2 * p₂) by ring]
      apply IsCoprime.add_mul_left_right
      apply IsCoprime.mul_right
      norm_num
      -- Now we shall prove that 3 and p₁ has gcd 1.
      rw [Int.isCoprime_iff_gcd_eq_one]
      rw [Int.gcd_comm, h₄] at h₀
      suffices Int.gcd 3 p₁ ∣ Int.gcd 60 p₁ by
        rw [h₀] at this
        simp_all
      rw [show (60 : ℤ) = 20 * 3 by norm_num]
      apply Int.gcd_dvd_gcd_mul_left
    -- We shall prove that 7 ∣ n.
    have h₁₀ : 7 ∣ n := by
      have h₁₀ : 7 ∣ p₃ * 420 := by
        calc
          7 ∣ 7 * (p₃ * 60) := by apply dvd_mul_right
          _ = p₃ * 420 := by ring
      rw [<-h₇] at h₁₀
      -- It suffices to show that 7 and (7p₁ + 6p₂) are coprime.
      apply IsCoprime.dvd_of_dvd_mul_left _ h₁₀
      -- It suffices to show that 7 and 6p₂ are coprime.
      rw [add_comm]
      apply IsCoprime.add_mul_left_right
      apply IsCoprime.mul_right
      norm_num
      -- Now we shall prove that 7 and p₂ has gcd 1.
      rw [Int.isCoprime_iff_gcd_eq_one]
      rw [Int.gcd_comm, h₅] at h₂
      suffices Int.gcd 7 p₂ ∣ Int.gcd 70 p₂ by
        rw [h₂] at this
        simp_all
      rw [show (70 : ℤ) = 10 * 7 by norm_num]
      apply Int.gcd_dvd_gcd_mul_left
    -- Now we can prove that 84 ∣ n.
    have h₁₁ : 4 * 3 * 7 ∣ n := by
      iterate 2 apply IsCoprime.mul_dvd (by norm_num)
      all_goals
        simp_all
    simp at h₁₁
    apply Int.le_of_dvd h₆ h₁₁
