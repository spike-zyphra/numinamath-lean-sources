import Mathlib

theorem algebra_4394 {a b : ℝ} (h : (a - 1)^2 + abs (a * b - 2) = 0) :
    ∑ i ∈ Finset.range 2017, (x / ((a + i) * (b + i))) = 2017 ↔ x = 2018 := by
  have h1 : (a - 1) ^ 2 = 0 := by
    linarith [abs_nonneg (a * b - 2), sq_nonneg (a - 1)]
  have ha1 : a = 1 := by
    nlinarith
  have h2 : abs (a * b - 2) = 0 := by
    linarith [abs_nonneg (a * b - 2), sq_nonneg (a - 1)]
  have h3 : a * b - 2 = 0 := by
    simpa [abs_eq_zero] using h2
  have h4 : a * b = 2 := by
    linarith
  have ha2 : b = 2 := by
    rw [ha1] at h4
    nlinarith
  rw [ha1] at *
  rw [ha2] at *
  constructor
  · -- Assume the summation equals 2017, prove x = 2018
    intro h_eq
    have h5 : ∑ i in Finset.range 2017, (x / ((1 + (i : ℝ)) * (2 + (i : ℝ)))) = x * (1 - 1 / (2018 : ℝ)) := by
      have h6 : ∀ (n : ℕ), ∑ i in Finset.range n, (x / ((1 + (i : ℝ)) * (2 + (i : ℝ)))) = x * (1 - 1 / ((↑n + 1 : ℝ))) := by
        intro n
        induction n with
        | zero =>
          simp
          <;> ring
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp
          ring
      specialize h6 2017
      norm_num at h6 ⊢
      linarith
    rw [h5] at h_eq
    linarith
  · -- Assume x = 2018, prove the summation equals 2017
    intro h_eq
    have h5 : ∑ i in Finset.range 2017, (x / ((1 + (i : ℝ)) * (2 + (i : ℝ)))) = x * (1 - 1 / (2018 : ℝ)) := by
      have h6 : ∀ (n : ℕ), ∑ i in Finset.range n, (x / ((1 + (i : ℝ)) * (2 + (i : ℝ)))) = x * (1 - 1 / ((↑n + 1 : ℝ))) := by
        intro n
        induction n with
        | zero =>
          simp
          <;> ring
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp
          ring
      specialize h6 2017
      norm_num at h6 ⊢
      linarith
    rw [h5, h_eq]
    norm_num