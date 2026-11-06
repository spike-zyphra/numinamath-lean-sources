import Mathlib

theorem algebra_298463 (a b : ℝ) (ha : a ≠ b)
    (h : ∀ x : ℝ, (x^2 + 20 * a * x + 10 * b) * (x^2 + 20 * b * x + 10 * a) ≠ 0) :
    ¬ ∃ n : ℤ, 20 * (b - a) = n := by 
  intro h3
  rcases h3 with ⟨n, hn⟩
  have h1 : (20 * a) ^ 2 - 4 * (10 * b) < 0 := by
    by_contra h1
    push_neg at h1
    have h2 : ∃ x : ℝ, x ^ 2 + 20 * a * x + 10 * b = 0 := by
      use (-20 * a + Real.sqrt ((20 * a) ^ 2 - 4 * (10 * b))) / 2
      nlinarith [Real.sqrt_nonneg ((20 * a) ^ 2 - 4 * (10 * b)), Real.sq_sqrt (show (0 : ℝ) ≤ (20 * a) ^ 2 - 4 * (10 * b) by linarith)]
    rcases h2 with ⟨x, hx⟩
    have h3 : (x ^ 2 + 20 * a * x + 10 * b) * (x ^ 2 + 20 * b * x + 10 * a) = 0 := by
      rw [show x ^ 2 + 20 * a * x + 10 * b = 0 by linarith [hx]]
      norm_num
    have h4 : (x ^ 2 + 20 * a * x + 10 * b) * (x ^ 2 + 20 * b * x + 10 * a) ≠ 0 := h x
    contradiction
  have h2' : (20 * b) ^ 2 - 4 * (10 * a) < 0 := by
    by_contra h2
    push_neg at h2
    have h3 : ∃ x : ℝ, x ^ 2 + 20 * b * x + 10 * a = 0 := by
      use (-20 * b + Real.sqrt ((20 * b) ^ 2 - 4 * (10 * a))) / 2
      nlinarith [Real.sqrt_nonneg ((20 * b) ^ 2 - 4 * (10 * a)), Real.sq_sqrt (show (0 : ℝ) ≤ (20 * b) ^ 2 - 4 * (10 * a) by linarith)]
    rcases h3 with ⟨x, hx⟩
    have h4 : (x ^ 2 + 20 * a * x + 10 * b) * (x ^ 2 + 20 * b * x + 10 * a) = 0 := by
      rw [show x ^ 2 + 20 * b * x + 10 * a = 0 by linarith [hx]]
      ring_nf
    have h5 : (x ^ 2 + 20 * a * x + 10 * b) * (x ^ 2 + 20 * b * x + 10 * a) ≠ 0 := h x
    contradiction
  have h4 : n < 1 := by
    by_contra h4
    push_neg at h4
    have h5 : n ≥ 1 := by omega
    have h6 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h5
    have h7 : (20 * (b - a) : ℝ) ≥ (1 : ℝ) := by
      linarith
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
      intro h4
      apply ha
      linarith
    ), sq_nonneg (a - b), sq_nonneg (a + b)]
  have h4' : n > -1 := by
    by_contra h4
    push_neg at h4
    have h5 : n ≤ -1 := by omega
    have h6 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h5
    have h7 : (20 * (b - a) : ℝ) ≤ (-1 : ℝ) := by
      linarith
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
      intro h4
      apply ha
      linarith
    ), sq_nonneg (a - b), sq_nonneg (a + b)]
  have h4b' : n = 0 := by 
    omega
  have h4b : (20 * (b - a) : ℝ) = (0 : ℝ) := by
    have h12 : (n : ℝ) = (0 : ℝ) := by
      exact_mod_cast (show (n : ℝ) = (0 : ℝ) by
        exact_mod_cast (show n = (0 : ℤ) by omega)
      )
    linarith
  nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
    intro h4
    apply ha
    linarith
  ), sq_nonneg (a - b), sq_nonneg (a + b)]