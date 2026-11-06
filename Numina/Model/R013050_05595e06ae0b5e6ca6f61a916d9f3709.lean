import Mathlib

open Real

theorem algebra_320366 {a : ℕ → ℝ} (ha : ∀ n, a n > 0)
    (hsum : ∀ n, ∑ i in Finset.range n, a i = n ^ 2) :
    ∑ i in Finset.range 998, 1 / (sqrt (a i) + sqrt (a (i + 1))) = (sqrt 1997 - 1) / 2 := by

  have h1 : ∀ n, a n = 2 * (↑n : ℝ) + 1 := by
    intro n
    have h5 : ∑ i in Finset.range (n + 1), a i = ∑ i in Finset.range n, a i + a n := by
      rw [Finset.sum_range_succ]
    have h6 := hsum (n + 1)
    have h7 := hsum n
    rw [h5] at h6
    have eq1 : a n = (↑n + 1 : ℝ) ^ 2 - (↑n : ℝ) ^ 2 := by
      simp at h6 h7 ⊢
      nlinarith
    have eq2 : a n = 2 * (↑n : ℝ) + 1 := by
      nlinarith
    exact eq2
  have h2 : ∀ (i : ℕ), 1 / (sqrt (a i) + sqrt (a (i + 1))) = (sqrt (a (i + 1)) - sqrt (a i)) / 2 := by
    intro i
    have ha3 : a i = 2 * (↑i : ℝ) + 1 := h1 i
    have ha4 : a (i + 1) = 2 * (↑i + 1 : ℝ) + 1 := by
      specialize h1 (i + 1)
      simpa using h1
    rw [ha3, ha4]
    have ha5 : 0 < (2 * (↑i : ℝ) + 1 : ℝ) := by
      have h10 : a i > 0 := ha i
      rw [show a i = (2 * (↑i : ℝ) + 1 : ℝ) by nlinarith [h1 i]] at h10
      nlinarith
    have ha6 : 0 < (2 * ((↑i : ℝ) + 1) + 1 : ℝ) := by
      have h10 : a (i + 1) > 0 := ha (i + 1)
      rw [show a (i + 1) = (2 * (↑i + 1 : ℝ) + 1 : ℝ) by nlinarith [h1 (i + 1)]] at h10
      nlinarith
    have eq1 : 1 / (sqrt (2 * (↑i : ℝ) + 1) + sqrt (2 * ((↑i : ℝ) + 1) + 1)) = (sqrt (2 * ((↑i : ℝ) + 1) + 1) - sqrt (2 * (↑i : ℝ) + 1)) / 2 := by
      have ha8 : sqrt (2 * (↑i : ℝ) + 1) + sqrt (2 * ((↑i : ℝ) + 1) + 1) ≠ 0 := by
        have h9 : sqrt (2 * (↑i : ℝ) + 1) ≥ 0 := by positivity
        have h10 : sqrt (2 * ((↑i : ℝ) + 1) + 1) ≥ 0 := by positivity
        have h11 : sqrt (2 * (↑i : ℝ) + 1) + sqrt (2 * ((↑i : ℝ) + 1) + 1) > 0 := by
          have h12 : sqrt (2 * (↑i : ℝ) + 1) ≥ 0 := by positivity
          have h13 : sqrt (2 * ((↑i : ℝ) + 1) + 1) ≥ 0 := by positivity
          nlinarith [Real.sqrt_nonneg (2 * (↑i : ℝ) + 1), Real.sqrt_nonneg (2 * ((↑i : ℝ) + 1) + 1),
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (↑i : ℝ) + 1) by linarith [ha5]), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * ((↑i : ℝ) + 1) + 1) by linarith [ha6])]
        linarith
      field_simp [show sqrt (2 * (↑i : ℝ) + 1) + sqrt (2 * ((↑i : ℝ) + 1) + 1) ≠ 0 by assumption]
      have h30 : 0 ≤ (2 * (↑i : ℝ) + 1 : ℝ) := by linarith [ha5]
      have h31 : 0 ≤ (2 * ((↑i : ℝ) + 1) + 1 : ℝ) := by linarith [ha6]
      have h32 : sqrt (2 * (↑i : ℝ) + 1) ^ 2 = (2 * (↑i : ℝ) + 1 : ℝ) := by
        rw [Real.sq_sqrt]
        nlinarith
      have h33 : sqrt (2 * ((↑i : ℝ) + 1) + 1) ^ 2 = (2 * ((↑i : ℝ) + 1) + 1 : ℝ) := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [Real.sqrt_nonneg (2 * (↑i : ℝ) + 1), Real.sqrt_nonneg (2 * ((↑i : ℝ) + 1) + 1),
        sq_nonneg (sqrt (2 * (↑i : ℝ) + 1) - sqrt (2 * ((↑i : ℝ) + 1) + 1)), sq_nonneg (sqrt (2 * (↑i : ℝ) + 1) + sqrt (2 * ((↑i : ℝ) + 1) + 1))
      ]
    exact eq1
  have h3 : ∑ i in Finset.range 998, 1 / (sqrt (a i) + sqrt (a (i + 1))) = ∑ i in Finset.range 998, (sqrt (a (i + 1)) - sqrt (a i)) / 2 := by
    apply Finset.sum_congr
    . rfl
    intro i h4
    rw [h2 i]
  rw [h3]
  have h4 : ∀ n : ℕ, ∑ i in Finset.range n, (sqrt (a (i + 1)) - sqrt (a i)) / 2 = (sqrt (a n) - sqrt (a 0)) / 2 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      all_goals
        ring
  specialize h4 998
  rw [h4]
  have ha0 : a 0 = 1 := by
    have ha0 : a 0 = 2 * (↑(0 : ℕ) : ℝ) + 1 := h1 0
    norm_num at ha0 ⊢
    linarith
  have ha998 : a 998 = (1997 : ℝ) := by
    have ha998 : a 998 = 2 * (↑(998 : ℕ) : ℝ) + 1 := h1 998
    norm_num at ha998 ⊢
    linarith
  rw [ha0, ha998]
  have h13 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
  rw [h13]
  all_goals
    ring