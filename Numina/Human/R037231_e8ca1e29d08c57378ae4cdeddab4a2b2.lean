import Mathlib

/- What is the largest $x$ such that $x^{2}$ divides $24 \cdot 35 \cdot 46 \cdot 57$ ?-/
theorem number_theory_608420 :
    IsGreatest {x : ℕ | x ^ 2 ∣ 24 * 35 * 46 * 57} 12 := by
  -- Simplify the goal into two parts.
  simp only [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  .  -- Verify that 12^2 divides 24 * 35 * 46 * 57.
    simp
    norm_num
  . -- Show that x is not less than 12.
    simp
    intro x hx
    rw [show (2202480 : ℕ) = 12 ^ 2 * (5 * 7 * 19 * 23) by norm_num, dvd_iff_exists_eq_mul_right] at hx
    obtain ⟨c, hx⟩ := hx
    -- Show that 5 ∣ c.
    have h₀ : 5 ∣ c := by
      -- We have 5 ∣ x²c, but 5 ∤ x².
      have h₁ : 5 ∣ x ^ 2 * c := by
        calc
          5 ∣ 5 * (12 ^ 2 * 7 * 19 * 23) := by apply Nat.dvd_mul_right
          _ = x ^ 2 * c := by linarith
      apply Prime.dvd_or_dvd (Nat.prime_iff.mp Nat.prime_five) at h₁
      -- Show that 5 ∤ x².
      have h₂ : ¬5 ∣ x ^ 2 := by
        by_contra!
        -- Assume on the contrary that 5 ∣ x², then 25 ∣ x² and contradiction could be derived.
        apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_five) at this
        rw [<-Nat.pow_dvd_pow_iff (show 2 ≠ 0 by norm_num)] at this
        have habsurd : 5 ^ 2 ∣ 5 * (12 ^ 2 * 7 * 19 * 23) := by
          rw [show 5 * (12 ^ 2 * 7 * 19 * 23) = x ^ 2 * c by linarith]
          calc
            5 ^ 2 ∣ x ^ 2 := this
            _ ∣ x ^ 2 * c := by
              apply Nat.dvd_mul_right
        norm_num at habsurd
      tauto
    -- Show that 7 ∣ c.
    have h₁ : 7 ∣ c := by
      -- We have 7 ∣ x²c, but 7 ∤ x².
      have h₀ : 7 ∣ x ^ 2 * c := by
        calc
          7 ∣ 7 * (12 ^ 2 * 5 * 19 * 23) := by apply Nat.dvd_mul_right
          _ = x ^ 2 * c := by linarith
      apply Prime.dvd_or_dvd (Nat.prime_iff.mp (show Nat.Prime 7 by decide)) at h₀
      -- Show that 7 ∤ x².
      have h₂ : ¬7 ∣ x ^ 2 := by
        by_contra!
        -- Assume on the contrary that 7 ∣ x², then 49 ∣ x² and contradiction could be derived.
        apply Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 7 by decide) at this
        rw [<-Nat.pow_dvd_pow_iff (show 2 ≠ 0 by norm_num)] at this
        have habsurd : 7 ^ 2 ∣ 7 * (12 ^ 2 * 5 * 19 * 23) := by
          rw [show 7 * (12 ^ 2 * 5 * 19 * 23) = x ^ 2 * c by linarith]
          calc
            7 ^ 2 ∣ x ^ 2 := this
            _ ∣ x ^ 2 * c := by
              apply Nat.dvd_mul_right
        norm_num at habsurd
      tauto
    -- Show that 19 ∣ c.
    have h₂ : 19 ∣ c := by
      -- We have 19 ∣ x²c, but 19 ∤ x².
      have h₀ : 19 ∣ x ^ 2 * c := by
        calc
          19 ∣ 19 * (12 ^ 2 * 5 * 7 * 23) := by apply Nat.dvd_mul_right
          _ = x ^ 2 * c := by linarith
      apply Prime.dvd_or_dvd (Nat.prime_iff.mp (show Nat.Prime 19 by decide)) at h₀
      -- Show that 19 ∤ x².
      have h₃ : ¬19 ∣ x ^ 2 := by
        by_contra!
        -- Assume on the contrary that 19 ∣ x², then 361 ∣ x² and contradiction could be derived.
        apply Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 19 by decide) at this
        rw [<-Nat.pow_dvd_pow_iff (show 2 ≠ 0 by norm_num)] at this
        have habsurd : 19 ^ 2 ∣ 19 * (12 ^ 2 * 5 * 7 * 23) := by
          rw [show 19 * (12 ^ 2 * 5 * 7 * 23) = x ^ 2 * c by linarith]
          calc
            19 ^ 2 ∣ x ^ 2 := this
            _ ∣ x ^ 2 * c := by
              apply Nat.dvd_mul_right
        norm_num at habsurd
      tauto
    -- Show that 23 ∣ c.
    have h₃ : 23 ∣ c := by
      -- We have 23 ∣ x²c, but 23 ∤ x².
      have h₀ : 23 ∣ x ^ 2 * c := by
        calc
          23 ∣ 23 * (12 ^ 2 * 5 * 7 * 19) := by apply Nat.dvd_mul_right
          _ = x ^ 2 * c := by linarith
      apply Prime.dvd_or_dvd (Nat.prime_iff.mp (show Nat.Prime 23 by decide)) at h₀
      -- Show that 23 ∤ x².
      have h₄ : ¬23 ∣ x ^ 2 := by
        by_contra!
        -- Assume on the contrary that 23 ∣ x², then 529 ∣ x² and contradiction could be derived.
        apply Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 23 by decide) at this
        rw [<-Nat.pow_dvd_pow_iff (show 2 ≠ 0 by norm_num)] at this
        have habsurd : 23 ^ 2 ∣ 23 * (12 ^ 2 * 5 * 7 * 19) := by
          rw [show 23 * (12 ^ 2 * 5 * 7 * 19) = x ^ 2 * c by linarith]
          calc
            23 ^ 2 ∣ x ^ 2 := this
            _ ∣ x ^ 2 * c := by
              apply Nat.dvd_mul_right
        norm_num at habsurd
      tauto
    -- Show that 5 * 7 * 19 * 23 ∣ c.
    have h₅ : 5 * 7 * 19 * 23 ∣ c := by
      -- We have 5 ∣ c, 7 ∣ c, 19 ∣ c, and 23 ∣ c, so we can use the property of coprime numbers.
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      . norm_num
      . apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        . norm_num
        . apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
          . norm_num
          . exact h₀
          . exact h₁
        . exact h₂
      . exact h₃
    -- Show that c is not less than 5 * 7 * 19 * 23.
    apply Nat.le_of_dvd at h₅
    -- Therefore, x ≤ 12.
    nlinarith
    -- Verify that 0 < c.
    by_contra!
    simp at this
    simp [this] at hx