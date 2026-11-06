import Mathlib

theorem algebra_610096
    (P : Polynomial ℤ)
    (h_coeffs_nonneg : ∀ n : ℕ, 0 ≤ P.coeff n)
    (h_coeffs_lt_100 : ∀ n : ℕ, P.coeff n < 100)
    (hP10 : P.eval (10 : ℤ) = 331633)
    (hPneg10 : P.eval (-10 : ℤ) = 273373)
    : P.eval (1 : ℤ) = 100 := by

  -- Calculate S = P(10) + P(-10) and D = P(10) - P(-10)
  let S := P.eval 10 + P.eval (-10)
  let D := P.eval 10 - P.eval (-10)

  have hS : S / 2 = ∑ i ∈ Finset.range (P.natDegree + 1), (if Even i then P.coeff i * 10^i else 0) := by
    have hS_even : ∀ i : ℕ, Even i → P.coeff i * 10 ^ i + P.coeff i * (-10) ^ i = 2 * P.coeff i * 10 ^ i := by
      intro i h_even
      have := Even.neg_pow h_even (-10)
      simp at this
      rw [←this]
      linarith

    have hS_odd : ∀ i : ℕ, Odd i → P.coeff i * 10 ^ i + P.coeff i * (-10) ^ i = 0 := by
      intro i h_odd
      have := Odd.neg_pow h_odd (-10)
      simp at this
      rw [this]
      linarith

    have : S = 2 * (∑ i ∈ Finset.range (P.natDegree + 1), (if Even i then P.coeff i * 10^i else 0)) := by
      rw [Finset.mul_sum]
      unfold S
      simp only [Polynomial.eval_eq_sum_range]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro x hx
      split_ifs with h_even
      . rw [hS_even x h_even]
        linarith
      . simp at h_even
        rw [hS_odd x h_even]
        linarith

    rw [this]
    simp

  have hD : D / 2 = ∑ i ∈ Finset.range (P.natDegree + 1), (if Odd i then P.coeff i * 10^i else 0) := by
    have hD_even : ∀ i : ℕ, Even i → P.coeff i * 10 ^ i - P.coeff i * (-10) ^ i = 0 := by
      intro i h_even
      have := Even.neg_pow h_even (-10)
      simp at this
      rw [←this]
      linarith

    have hD_odd : ∀ i : ℕ, Odd i → P.coeff i * 10 ^ i - P.coeff i * (-10) ^ i = 2 * P.coeff i * 10 ^ i := by
      intro i h_odd
      have := Odd.neg_pow h_odd (-10)
      simp at this
      rw [this]
      linarith

    have : D = 2 * (∑ i ∈ Finset.range (P.natDegree + 1), (if Odd i then P.coeff i * 10^i else 0)) := by
      rw [Finset.mul_sum]
      unfold D
      simp only [Polynomial.eval_eq_sum_range]
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl]
      intro x hx
      split_ifs with h_odd
      . rw [hD_odd x h_odd]
        linarith
      . simp at h_odd
        rw [hD_even x h_odd]
        linarith

    rw [this]
    simp

  have hS_ge : ∀ i : ℕ, S / 2 ≥ (if Even i then P.coeff i * 10^i else 0) := by
    intro i
    by_cases h : P.natDegree < i
    . rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
      omega
    . push_neg at h
      rw [hS]
      have hf : ∀ j ∈ Finset.range (P.natDegree + 1), 0 ≤ (if Even j then P.coeff j * 10^j else 0) := by
        intro j hj
        split_ifs with h_even
        . apply mul_nonneg
          . apply h_coeffs_nonneg j
          . apply pow_nonneg (by positivity)
        . omega
      have ha : i ∈ Finset.range (P.natDegree + 1) := by simp; omega
      exact Finset.single_le_sum hf ha

  have hD_ge : ∀ i : ℕ, D / 2 ≥ (if Odd i then P.coeff i * 10^i else 0) := by
    intro i
    by_cases h : P.natDegree < i
    . rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
      omega
    . push_neg at h
      rw [hD]
      have hf : ∀ j ∈ Finset.range (P.natDegree + 1), 0 ≤ (if Odd j then P.coeff j * 10^j else 0) := by
        intro j hj
        split_ifs with h_odd
        . apply mul_nonneg
          . apply h_coeffs_nonneg j
          . apply pow_nonneg (by positivity)
        . omega
      have ha : i ∈ Finset.range (P.natDegree + 1) := by simp; omega
      exact Finset.single_le_sum hf ha

  -- Prove that all even coefficients ≥ 6 are zero
  have higher_even_coeffs_zero : ∀ k : ℕ, k ≥ 3 → P.coeff (2 * k) = 0 := by
    intro k hk
    by_contra h_pos
    push_neg at h_pos
    have : P.coeff (2 * k) >= 0 := h_coeffs_nonneg (2 * k)
    have : P.coeff (2 * k) >= 1 := by omega
    have : S / 2 >= P.coeff (2*k) * (10 ^ (2*k)) := by
      have := hS_ge (2*k)
      simp at this
      exact this
    have : 10 ^ (2*k) >= 10 ^ 6 := by
      apply Nat.pow_le_pow_right
      . positivity
      . omega
    have : S / 2 ≥ 10 ^ 6 := by nlinarith
    omega

  have higher_odd_coeffs_zero : ∀ k : ℕ, k ≥ 2 → P.coeff (2 * k + 1) = 0 := by
    intro k hk
    by_contra h_pos
    push_neg at h_pos
    have : P.coeff (2 * k + 1) >= 0 := h_coeffs_nonneg (2 * k + 1)
    have : P.coeff (2 * k + 1) >= 1 := by omega
    have : D / 2 >= P.coeff (2*k+1) * (10 ^ (2*k+1)) := by
      have := hD_ge (2*k+1)
      simp at this
      exact this
    have : 10^(2*k+1)>=10^5 := by
      apply Nat.pow_le_pow_right
      . positivity
      . omega
    have : D / 2 >= 10^5 := by nlinarith
    omega

  have higher_coeffs_zero : ∀ k : ℕ, 5 ≤ k → P.coeff k = 0 :=
    fun k hk => by
      -- Case analysis: k is either even or odd
      by_cases h : Even k
      · -- Case: k is even (k = 2j for some j)
        -- Get the definition of evenness
        rcases h with ⟨j, hj⟩
        rw [hj, ← two_mul]
        -- Use higher_even_coeffs_zero
        apply higher_even_coeffs_zero j
        linarith
      · -- Case: k is odd (k = 2j + 1 for some j)
        -- If k is not even, it's odd
        simp at h
        -- Express k in terms of j
        rcases h with ⟨j, hj⟩
        rw [hj]

        -- Use higher_odd_coeffs_zero
        apply higher_odd_coeffs_zero j
        linarith

  have hn: P.natDegree < 5 := by
    by_contra h_contra
    simp at h_contra
    have := higher_coeffs_zero P.natDegree h_contra
    simp at this
    have : P.eval 10 = 0 := by
      rw [this]
      simp
    linarith

  have : P.coeff 0 < 100 := h_coeffs_lt_100 0
  have : P.coeff 1 < 100 := h_coeffs_lt_100 1
  have : P.coeff 2 < 100 := h_coeffs_lt_100 2
  -- have : P.coeff 3 < 100 := h_coeffs_lt_100 3
  -- have : P.coeff 4 < 100 := h_coeffs_lt_100 4

  have : P.coeff 0 ≥ 0 := h_coeffs_nonneg 0
  have : P.coeff 1 ≥ 0 := h_coeffs_nonneg 1
  have : P.coeff 2 ≥ 0 := h_coeffs_nonneg 2
  -- have : P.coeff 3 ≥ 0 := h_coeffs_nonneg 3
  -- have : P.coeff 4 ≥ 0 := h_coeffs_nonneg 4

  have h2: Even 2 := by simp
  have h2': ¬ Odd 2 := by simp
  have h3: Odd 3 := by exact odd_two_mul_add_one 1
  have h3': ¬ Even 3 := by simp; exact h3
  have h4: Even 4 := by exact even_two_mul 2
  have h4': ¬ Odd 4 := by simp; exact h4

  have hn4: P.natDegree = 4 := by
    by_contra h_contra
    simp at h_contra
    have : S / 2 <= ∑ i ∈ Finset.range (4), if Even i then P.coeff i * 10 ^ i else 0 := by
      rw [hS]
      have h : Finset.range (P.natDegree + 1) ⊆ Finset.range (4) := by simp; omega
      have hf : ∀ i ∈ Finset.range (4), i ∉ Finset.range (P.natDegree + 1) -> 0 ≤ (if Even i then P.coeff i * 10 ^ i else 0) := by
        intro i hi hi'
        split_ifs with h_even
        . have := h_coeffs_nonneg i
          positivity
        . omega
      exact Finset.sum_le_sum_of_subset_of_nonneg h hf

    repeat rw [Finset.sum_range_succ] at this
    simp [h3'] at this
    omega

  have : S/2 = P.coeff 0 + P.coeff 2 * 100 + P.coeff 4 * 10000 := by
    rw [hS, hn4]
    simp
    repeat rw [Finset.sum_range_succ]
    simp [h3, h4]

  have : D / 2 = P.coeff 1 * 10 + P.coeff 3 * 1000 := by
    rw [hD, hn4]
    simp
    repeat rw [Finset.sum_range_succ]
    simp [h2', h3, h4]

  have : D / 20 = P.coeff 1 + P.coeff 3 * 100 := by omega

  have hc0 : P.coeff 0 = 3 := by omega
  have hc1 : P.coeff 1 = 13 := by omega
  have hc2 : P.coeff 2 = 25 := by omega
  have hc3 : P.coeff 3 = 29 := by omega
  have hc4 : P.coeff 4 = 30 := by omega

  -- Now we know that P(x) = 3 + 13x + 25x² + 29x³ + 30x⁴
  -- Compute P(1) by summing all coefficients
  have h_P_expr : P.eval 1 = P.coeff 0 + P.coeff 1 + P.coeff 2 + P.coeff 3 + P.coeff 4 := by
    rw [Polynomial.eval_eq_sum_range' hn]
    have h_mul_one : ∀ i ∈ Finset.range (5), P.coeff i * 1 ^ i = P.coeff i := by
      intro i hi
      rw [one_pow, mul_one]
    rw [Finset.sum_congr rfl h_mul_one]
    simp [Finset.sum_range_succ]

  -- Calculate the sum
  have h_sum : P.coeff 0 + P.coeff 1 + P.coeff 2 + P.coeff 3 + P.coeff 4 = 100 := by
    rw [hc0, hc1, hc2, hc3, hc4]
    norm_num

  -- Conclude the proof
  rw [h_P_expr, h_sum]
