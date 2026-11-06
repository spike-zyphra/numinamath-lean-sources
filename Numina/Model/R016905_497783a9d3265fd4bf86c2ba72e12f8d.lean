import Mathlib

theorem algebra_165391 (x : ℕ) (hx : 0 < x) :
    ∑ i ∈ Finset.Icc 1 (x - 1), (i / x : ℝ) = 3 ↔ x = 7 := by
  constructor
  · -- Assume the summation equals 3, prove x equals 7
    intro h
    have h1 : x ≥ 1 := by linarith
    have h3 : x > 1 := by
      by_contra h4
      push_neg at h4
      have h4' : x = 1 := by linarith
      rw [h4'] at h
      norm_num [Finset.sum_eq_zero] at h
    have eq2 : ∀ (n : ℕ), n ≥ 2 → ∑ i in Finset.Icc 1 (n - 1), (i / (n : ℝ)) = (↑n - 1) / 2 := by
      intro n hn
      have h10 : n ≥ 2 := hn
      have h11 : ∑ i in Finset.Icc 1 (n - 1), (i / (n : ℝ)) = (∑ i in Finset.Icc 1 (n - 1), (i : ℝ)) / (n : ℝ) := by
        rw [Finset.sum_div]
      rw [h11]
      have h12 : ∑ i in Finset.Icc 1 (n - 1), (i : ℝ) = (↑n * (↑n - 1) / 2 : ℝ) := by
        have h13 : ∀ (k : ℕ), ∑ i in Finset.Icc 1 k, (i : ℝ) = (↑k * (↑k + 1) / 2 : ℝ) := by
          intro k
          induction k with
          | zero =>
            norm_num [Finset.sum_eq_zero]
          | succ k ih =>
            rw [Finset.sum_Icc_succ_top (by omega)]
            rw [ih]
            field_simp
            ring
        have h14 : n - 1 ≥ 1 := by omega
        have h17 : ∑ i in Finset.Icc 1 (n - 1), (i : ℝ) = (↑(n - 1) * (↑(n - 1) + 1) / 2 : ℝ) := by
          specialize h13 (n - 1)
          simpa using h13
        rw [h17]
        field_simp at *
        ring
      rw [h12]
      field_simp at *
      ring
    have eq2' : ∑ i in Finset.Icc 1 (x - 1), (i / x : ℝ) = (↑x - 1) / 2 := by
      have h100 : x ≥ 2 := by linarith
      specialize eq2 x h100
      simpa using eq2
    rw [eq2'] at h
    have eq3 : (x : ℝ) = 7 := by
      nlinarith
    have eq4 : x = 7 := by
      exact_mod_cast eq3
    exact eq4
  · -- Assume x = 7, prove the summation equals 3
    intro h
    rw [h]
    norm_num [Finset.sum_Icc_succ_top]