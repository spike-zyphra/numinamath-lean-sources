import Mathlib

theorem number_theory_15570 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ ∃ p q : ℕ, (n : ℝ) / 475 = (p : ℝ) / 10 ^ q} = 24 := by
  have AB_eq : {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ ∃ p q : ℕ, (n : ℝ) / 475 = (p : ℝ) / 10 ^ q} = {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ 19 ∣ n} := by
    ext n
    simp
    intro _ _
    apply Iff.intro <;> intro h
    -- case1 : n / 475 = p / 10 ^ q => n = 19 * m
    . obtain ⟨p, q, hpq⟩ := h
      -- Exclude the denominator from the expression to n*10^q = 19*(25*p)
      have eq₁ : (n : ℝ) * 10 ^ q = 19 * (25 * p) := by
        calc
          n * 10 ^ q = 475 * ((n : ℝ) / 475) * 10 ^ q := by rw [mul_div_cancel₀]; norm_num
          _ = 475 * ((p / 10 ^ q) * 10 ^ q) := by rw [hpq]; ring_nf
          _ = 475 * p := by rw [div_mul_cancel₀]; positivity
          _ = 19 * (25 * p) := by ring_nf
      replace eq₁ : (n : ℤ) * 10 ^ q = 19 * (25 * p) := by norm_cast at eq₁ ⊢
      -- by equation above, we have n * 10 ^ q divided by 19
      have dvd₁ : 19 ∣ (n : ℤ) * 10 ^ q := by
        rw [eq₁]
        apply dvd_mul_right
      -- show that 19 and 10 ^ q is coprime
      have coprime₁ : IsCoprime (19 : ℤ) (10 ^ q) := by
        have coprime : IsCoprime 19 (10 : ℤ) := by rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
        apply IsCoprime.pow_right
        exact coprime
      -- by the 19.coprime 10, we simply to 19 ∣ n
      apply IsCoprime.dvd_of_dvd_mul_right at dvd₁
      norm_cast at dvd₁
      exact coprime₁
    -- case2 : n = 19 * m => n / 475 = p / 10 ^ q
    . obtain ⟨m, hn⟩ := h
      use (4 * m)
      use (2)
      rw [hn]
      field_simp
      ring_nf
  rw [AB_eq]
  have : {n : ℕ | 1 ≤ n ∧ n ≤ 474 ∧ 19 ∣ n} = Finset.filter (λ n => 19 ∣ n) (Finset.Icc 1 474) := by
    ext n
    simp
    <;> tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide