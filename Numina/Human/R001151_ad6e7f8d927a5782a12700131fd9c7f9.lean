import Mathlib

open Polynomial

theorem algebra_20751 {Q : ℤ[X]} (hQ : ∀ n, Q.coeff n ≥ 0)
    (hQ1 : Q.eval 1 = 4) (hQ2 : Q.eval 5 = 152) : Q.eval 6 = 254 := by
  -- since all coefficients are non-negative, Q ≥ corresponding coeff times x^n
  have h1 (n m : ℕ) : Q.eval ↑m ≥ (Q.coeff n) * m^n := by
    have hh1: Q = Q.erase n + ((Q.coeff n) * ↑X^n) := by
      rw [Polynomial.ext_iff]
      intro n'
      by_cases hn: n'=n
      repeat simp [hn]
    nth_rw 1 [hh1]; simp
    rw [Polynomial.eval_eq_sum]
    apply Finset.sum_nonneg
    intro i _; simp
    apply mul_nonneg
    · by_cases hn: i = n
      · rw [hn]; simp
      rw [Polynomial.erase_ne _ _ _ hn]
      apply hQ
    · simp

  -- therefore degree of Q ≤ 3, otherwise Q 5 > 152
  have h2: Q.degree ≤ 3 := by
    by_contra! hc
    replace hc: Q.degree ≥ 4 := by
      exact Order.le_of_pred_lt hc
    have hh1: Q.eval 5 ≥ Q.coeff Q.natDegree * 5^Q.natDegree := by
      apply h1
    have hh2: Q.coeff Q.natDegree * 5^Q.natDegree ≥ 625 := by
      have tt1: Q.coeff Q.natDegree ≥ 1 := by
        have: Q.coeff Q.natDegree > 0 := by
          have htt1: Q.coeff Q.natDegree ≠ 0 := by
            have: Q ≠ 0 := by
              by_contra! hc; rw [hc] at hQ1; simp at hQ1
            simp [this]
          exact lt_of_le_of_ne (hQ Q.natDegree) (id (Ne.symm htt1))
        exact this
      have tt3: (5:ℤ)^Q.natDegree ≥ 625 := by
        rw [show (625:ℤ) = 5^4 by norm_num]
        apply (pow_le_pow_iff_right₀ (by norm_num)).mpr
        apply Polynomial.le_natDegree_of_coe_le_degree hc
      rw [← one_mul 625]
      apply mul_le_mul tt1 tt3 (by norm_num) (by linarith [tt1])
    linarith

  -- so Q = a3x^3+a2x^2+a1x+a0
  obtain ⟨a₃, ha₃, pa₃⟩ := show ∃ a : ℤ, a = Q.coeff 3 ∧ 0 ≤ a by simp; apply hQ
  obtain ⟨a₂, ha₂, pa₂⟩ := show ∃ a : ℤ, a = Q.coeff 2 ∧ 0 ≤ a by simp; apply hQ
  obtain ⟨a₁, ha₁, pa₁⟩ := show ∃ a : ℤ, a = Q.coeff 1 ∧ 0 ≤ a by simp; apply hQ
  obtain ⟨a₀, ha₀, pa₀⟩ := show ∃ a : ℤ, a = Q.coeff 0 ∧ 0 ≤ a by simp; apply hQ
  have hq_def: Q = a₃ * ↑X^3 + a₂ *↑X^2 + a₁ * ↑X + a₀ := by
    rw [ha₃, ha₂, ha₁, ha₀]
    rw [Polynomial.ext_iff]; intro n
    have hz {m m' : ℕ} (hm: m ≠ 0) : (Q.coeff m': Polynomial ℤ).coeff m = 0 := by
      apply Polynomial.coeff_C_ne_zero hm
    by_cases hn: n > 3
    · simp
      rw [if_neg, if_neg]; any_goals linarith
      have hh1: Q.coeff 1 * X.coeff n = 0 := by
        simp; right
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simp; linarith
      rw [hh1]; simp
      have hh2: Q.coeff n = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        apply lt_of_le_of_lt h2
        simp [hn]
      rw [hh2, hz]
      linarith

    push_neg at hn
    interval_cases n <;> simp
    · apply Polynomial.coeff_C_ne_zero (by simp)
    · rw [hz (by simp), hz (by simp)]; simp
    · rw [hz (by simp), hz (by simp)]; simp

  rw [hq_def] at hQ1 hQ2 ⊢
  simp at hQ1 hQ2 ⊢
  omega
