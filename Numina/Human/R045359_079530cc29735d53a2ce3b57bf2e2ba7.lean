import Mathlib

set_option maxHeartbeats 0

def is_norwegian (n : ℕ) := 0 < n ∧ ∃ x y z, 0 < x ∧ x < y ∧ y < z ∧ x ∣ n ∧ y ∣ n ∧ z ∣ n ∧ x + y + z = 2022

/- A number is called Norwegian if it has three distinct positive divisors whose sum is equal to 2022. Determine the smallest Norwegian number. (Note: The total number of positive divisors of a Norwegian number is allowed to be larger than 3.) (Cyprus) -/
theorem number_theory_24367 :
    IsLeast {n | is_norwegian n} 1344 := by
  -- Simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  constructor
  . -- Show that 1344 is Norwegian.
    simp [is_norwegian]
    use 6
    simp
    use 672
    simp
    use 1344
    omega
  . -- Show that any N < 1344 is not Norwegian.
    intro N hn
    by_contra! h₀
    simp [is_norwegian] at hn
    obtain ⟨hn, x, hx, y, hy, z, hz, h₁, h₂, h₃, h₄⟩ := hn
    -- let (a, b, c) = (N / x, N / y, N / z).
    let a := N / x
    let b := N / y
    let c := N / z
    have ha : a * x = N := by
      simp [a]
      rw [Nat.div_mul_cancel h₁]
    have hb : b * y = N := by
      simp [b]
      rw [Nat.div_mul_cancel h₂]
    have hc : c * z = N := by
      simp [c]
      rw [Nat.div_mul_cancel h₃]
    have hc' : 0 < c := by
      replace hz : 0 < z := (hx.trans hy).trans hz
      simp only [c]
      rw [Nat.div_pos_iff]
      refine ⟨hz, Nat.le_of_dvd hn h₃⟩
    have hb' : c < b := by
      simp [c, b]
      apply Nat.div_lt_of_lt_mul
      apply Nat.lt_mul_of_div_lt
      rw [Nat.div_div_self h₂]
      exact hz
      omega
      apply Nat.div_pos (Nat.le_of_dvd hn h₂) (hx.trans hy)
    have ha' : b < a := by
      simp [b, a]
      apply Nat.div_lt_of_lt_mul
      apply Nat.lt_mul_of_div_lt
      rw [Nat.div_div_self h₁]
      exact hy
      omega
      apply Nat.div_pos (Nat.le_of_dvd hn h₁) hx
    -- We have 1 / a + 1 / b + 1 / c = 2022 / N.
    replace h₄ : (1 / a + 1 / b + 1 / c : ℚ) = 2022 / N := by
      simp [a, b, c, -one_div, show (N / x : ℕ) = (N / x : ℚ) by norm_cast, show (N / y : ℕ) = (N / y : ℚ) by norm_cast, show (N / z : ℕ) = (N / z : ℚ) by norm_cast]
      rw [one_div_div, one_div_div, one_div_div, <-add_div, <-add_div]
      norm_cast
      rw [h₄]
      norm_cast
    -- Do case analysis.
    by_cases hc' : c ≥ 2
    . replace hb' : b ≥ 3 := by
        omega
      replace ha' : a ≥ 4 := by
        omega
      have h₅ : (1 / a + 1 / b + 1 / c : ℚ) < (1 / a + 1 / b + 1 / c : ℚ) := by
        calc
          (1 / a + 1 / b + 1 / c : ℚ) ≤ (1 / 4 + 1 / 3 + 1 / 2 : ℚ) := by
            apply add_le_add
            apply add_le_add
            all_goals
              apply div_le_div₀
              <;> norm_cast
          _ < (2022 / 1344 : ℚ) := by norm_num
          _ < (2022 / N : ℚ) := by
            apply div_lt_div_of_pos_left
            all_goals
              norm_cast
          _ = (1 / a + 1 / b + 1 / c : ℚ) := h₄.symm
      exact lt_irrefl _ h₅
    . replace hc' : c = 1 := by
        omega
      by_cases hb' : b ≥ 4
      . replace ha' : a ≥ 5 := by
          omega
        have h₅ : (1 / a + 1 / b + 1 / c : ℚ) < (1 / a + 1 / b + 1 / c : ℚ) := by
          calc
            (1 / a + 1 / b + 1 / c : ℚ) ≤ (1 / 5 + 1 / 4 + 1 / 1 : ℚ) := by
              apply add_le_add
              apply add_le_add
              all_goals
                apply div_le_div₀
                <;> norm_cast
            _ < (2022 / 1344 : ℚ) := by norm_num
            _ < (2022 / N : ℚ) := by
              apply div_lt_div_of_pos_left
              all_goals
                norm_cast
            _ = (1 / a + 1 / b + 1 / c : ℚ) := h₄.symm
        exact lt_irrefl _ h₅
      . by_cases hb' : b = 3
        . -- We have a < 6.
          have ha'' : (1 / a + 1 / b + 1 / c : ℚ) > 1 / 6 + 1 / b + 1 / c := by
            calc
              (1 / a + 1 / b + 1 / c : ℚ) = 2022 / N := h₄
              _ > (2022 / 1344 : ℚ) := by
                rw [gt_iff_lt]
                apply div_lt_div_of_pos_left
                all_goals
                  norm_cast
              _ ≥ (1 / 6 + 1 / 3 + 1 : ℚ) := by norm_num
              _ ≥ (1 / 6 + 1 / b + 1 / c) := by
                rw [hb', hc']
                norm_cast
          simp [-one_div] at ha''
          norm_cast at ha''
          apply div_lt_div_of_pos_left (by positivity) (by positivity) (a := 1) at ha''
          rw [one_div_one_div, one_div_one_div] at ha''
          norm_cast at ha''
          replace ha' : a > 3 := by
            omega
          -- Contradiction no matter a = 4 or 5.
          interval_cases a
          . rw [hb', hc'] at h₄
            norm_num at h₄
            field_simp [show (N : ℚ) ≠ 0 by simp; omega] at h₄
            norm_cast at h₄
            have h₅ : 19 ∣ 2022 * 12 := by
              rw [<-h₄]
              apply dvd_mul_of_dvd_left
              rfl
            norm_num at h₅
          . rw [hb', hc'] at h₄
            norm_num at h₄
            field_simp [show (N : ℚ) ≠ 0 by simp; omega] at h₄
            norm_cast at h₄
            have h₅ : 23 ∣ 2022 * 15 := by
              rw [<-h₄]
              apply dvd_mul_of_dvd_left
              rfl
            norm_num at h₅
        . replace hb' : b = 2 := by
            omega
          -- We have a < 224.
          have ha'' : (1 / a + 1 / b + 1 / c : ℚ) > 1 / 224 + 1 / b + 1 / c := by
            calc
              (1 / a + 1 / b + 1 / c : ℚ) = 2022 / N := h₄
              _ > (2022 / 1344 : ℚ) := by
                rw [gt_iff_lt]
                apply div_lt_div_of_pos_left
                all_goals
                  norm_cast
              _ ≥ (1 / 224 + 1 / 2 + 1 : ℚ) := by norm_num
              _ ≥ (1 / 224 + 1 / b + 1 / c) := by
                rw [hb', hc']
                norm_cast
          simp [-one_div] at ha''
          norm_cast at ha''
          apply div_lt_div_of_pos_left (by positivity) (by positivity) (a := 1) at ha''
          rw [one_div_one_div, one_div_one_div] at ha''
          norm_cast at ha''
          -- We have (3a + 2)N = 1348(3a), hence 3a + 2 ∣ 1348 * 2 (depending on parity of a).
          rw [hb', hc'] at h₄
          field_simp [show (a : ℚ) ≠ 0 by norm_cast; omega] at h₄
          norm_cast at h₄
          replace h₄ : (3 * a + 2) * N = 1348 * (3 * a) := by
            ring_nf at h₄ ⊢
            exact h₄
          replace h₄ : (3 * a + 2) ∣ 1348 * (3 * a) := by
            rw [<-h₄]
            apply dvd_mul_of_dvd_left
            rfl
          -- Lemma: If n ∣ 1348 = 2² * 337, n > 4, then 337 ∣ n.
          have lm (n : ℕ) (hn₁ : n ∣ 1348) (hn₂ : n > 4) : 337 ∣ n := by
            by_contra! hn₃
            rw [<-Nat.Prime.coprime_iff_not_dvd] at hn₃
            apply Nat.Coprime.symm at hn₃
            rw [show 1348 = 4 * 337 by norm_num, Nat.Coprime.dvd_mul_right hn₃] at hn₁
            apply Nat.le_of_dvd at hn₁
            linarith only [hn₁, hn₂]
            norm_num
            native_decide -- Prove that 337 is prime.
          -- Separate into two cases: a is even or odd.
          by_cases h₅ : Even a
          . simp [Even] at h₅
            obtain ⟨a', h₅⟩ := h₅
            rw [h₅] at h₄
            rw [<-two_mul, show 3 * (2 * a') + 2 = (3 * a' + 1) * 2 by ring, Nat.mul_comm 2 a', <-Nat.mul_assoc, <-Nat.mul_assoc, Nat.mul_dvd_mul_iff_right (by norm_num), Nat.mul_assoc] at h₄
            rw [Nat.Coprime.dvd_mul_right] at h₄
            pick_goal 2
            . simp [Nat.coprime_iff_gcd_eq_one]
            apply lm (3 * a' + 1) at h₄
            simp only [true_implies, show 3 * a' + 1 > 4 by omega] at h₄
            -- Since 337 ∣ 3a' + 1, we have 3a' + 1 ≥ 337.
            apply Nat.le_of_dvd (by omega) at h₄
            replace h₄ : a ≥ 224 := by
              omega
            -- Arrive at a contradiciton.
            absurd h₄
            simp [ha'']
          . simp at h₅
            rw [Nat.Coprime.dvd_mul_right] at h₄
            pick_goal 2
            . simp [Nat.coprime_iff_gcd_eq_one]
              rw [Nat.odd_mul]
              refine ⟨by simp [Odd], h₅⟩
            apply lm (3 * a + 2) at h₄
            simp only [true_implies, show 3 * a + 2 > 4 by omega] at h₄
            -- Since 337 ∣ 3a + 2 and 337 ≠ 3a + 2, we have 3a + 2 ≥ 2 * 337.
            rw [dvd_iff_exists_eq_mul_left] at h₄
            obtain ⟨a', h₄⟩ := h₄
            have h₅ : a' ≠ 1 := by
              by_contra!
              rw [this] at h₄
              replace h₄ : 3 * a = 335 := by
                omega
              replace h₄ : 3 ∣ 335 := by
                rw [<-h₄]
                apply dvd_mul_of_dvd_left
                rfl
              omega
            have h₅ : a' ≥ 2 := by
              omega
            replace h₄ : a ≥ 224 := by
              omega
            -- Arrive at a contradiciton.
            absurd h₄
            simp [ha'']
