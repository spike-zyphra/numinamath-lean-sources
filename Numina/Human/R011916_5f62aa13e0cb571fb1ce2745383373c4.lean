import Mathlib

/- Exercise 12. Let $n$ be a positive odd integer and $k$ a strictly positive integer. Suppose that the number of positive divisors of $2 n$ that are less than or equal to $k$ is odd. Show that there exists a divisor $d$ of $2 n$ for which $k < d \leqslant 2 k$. -/

theorem number_theory_294774 (n k : ℕ) (h₀ : Odd n) (h₁ : 0 < k)
    (h₂ : Odd ({d ∈ (2 * n).divisors | d ≤ k}).card) :
    ∃ d, 0 < d ∧ d ≤ 2 * k ∧ d ∣ 2 * n ∧ k < d := by
  -- it suffices to find d', divisor of n in (k/2, k] range
  suffices ∃ d', d' ≤ k ∧ d' ∣ n ∧ k < 2 * d' by
    obtain ⟨d', hd_le_k, h_d_dvd_n, h_k_lt_two_d⟩ := this
    use 2 * d'
    and_intros
    . simp
      linarith
    . simpa
    . rwa [Nat.mul_dvd_mul_iff_left (by norm_num)]
    . assumption
  -- we will prove by contradiction, i.e. assume all divisor of n ≤ k are also ≤ k if multiiplied by 2
  by_contra h_no_d
  push_neg at h_no_d
  -- we will prove contradiction by showing that divisors of 2n ≤ k is even
  suffices Even ({d ∈ (2 * n).divisors | d ≤ k}).card by
    rw [← Nat.not_odd_iff_even] at this
    contradiction
  -- write the cardinality as sum of odd count and even count
  rw [← Finset.filter_card_add_filter_neg_card_eq_card Odd]
  simp
  rw [Finset.filter_filter, Finset.filter_filter ]
  -- proving that odd and even counts are equal is enough
  suffices (Finset.filter (fun a => a ≤ k ∧ Odd a) (2 * n).divisors).card =
      (Finset.filter (fun a => a ≤ k ∧ Even a) (2 * n).divisors).card by
    rw [this]
    ring_nf
    rw [mul_comm]
    simp
  -- define function f which will be used for cardinaltiy proof
  let f (n : ℕ) := 2 * n
  -- write the even ones as image of f from odd set
  have h_f_image : Finset.filter (fun a => a ≤ k ∧ Even a) (2 * n).divisors =
      (Finset.filter (fun a => a ≤ k ∧ Odd a) (2 * n).divisors).image f := by
    ext x
    simp
    constructor
    -- prove if x is from odd set, 2*x is in even set
    . rintro ⟨⟨h_x_dvd_two_n, h_ne_zero⟩, h_x_le_k, h_even_x⟩
      obtain ⟨y, hy⟩ := h_even_x
      use y
      ring_nf at hy
      rw [mul_comm] at hy
      simp [h_ne_zero, f, hy]
      and_intros
      . have : y ∣ x := by
          use 2
          linarith
        apply dvd_trans this h_x_dvd_two_n
      . linarith
      . rw [hy] at h_x_dvd_two_n
        rw [Nat.mul_dvd_mul_iff_left (by norm_num)] at h_x_dvd_two_n
        exact Odd.of_dvd_nat h₀ h_x_dvd_two_n
    -- prove if x is in even set, there is a y in odd set so that f(y) = x
    . rintro ⟨y, ⟨⟨⟨h_y_dvd_two, h_n_ne_zero⟩, h_y_le_k, h_odd_y⟩, h_f_y_x⟩⟩
      simp [f] at h_f_y_x
      simp [h_n_ne_zero]
      have h_y_dvd_n : y ∣ n := by
        apply Nat.Coprime.dvd_of_dvd_mul_left (m := 2)
        . exact Nat.coprime_two_right.mpr h_odd_y
        . assumption
      rw [← h_f_y_x]
      and_intros
      . rwa [Nat.mul_dvd_mul_iff_left (by norm_num)]
      . apply h_no_d
        . assumption
        . assumption
      . simp
  -- prove f is injective, so sets are equal in size
  rw [h_f_image, eq_comm]
  have h_f_inj : Function.Injective f := by
    rintro a b hab
    simpa [f] using hab
  apply Finset.card_image_of_injective _ h_f_inj