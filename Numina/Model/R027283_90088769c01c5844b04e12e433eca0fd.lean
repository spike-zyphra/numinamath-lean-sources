import Mathlib

theorem algebra_11047 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (h1 : a 0 = 4) (h2 : b 0 = 4)
    (h3 : a 3 = 1) (h4 : b 3 = 1) :
    a 1 > b 1 := by
  rcases ha with ⟨d, had⟩
  rcases hb with ⟨r, hbl⟩
  have eq1 : a 3 = a 0 + 3 * d := by
    rw [had 3]
    ring
  rw [h1] at eq1
  have eq2 : 4 + 3 * d = 1 := by linarith [h3, eq1]
  have d_eq : d = -1 := by
    linarith
  have eq3 : b 3 = b 0 * r ^ 3 := hbl 3
  rw [h2] at eq3
  have eq4 : 4 * r ^ 3 = 1 := by
    linarith [h4, eq3]
  have a1_eq : a 1 = 3 := by
    have eq11 : a 1 = a 0 + d * (1 : ℕ) := by
      specialize had 1
      simpa using had
    rw [h1, d_eq] at eq11
    norm_num at eq11 ⊢
    linarith
  have b1_eq : b 1 = 4 * r := by
    specialize hbl 1
    rw [h2] at hbl
    simpa using hbl
  rw [a1_eq, b1_eq]
  have r_lt_34 : r < (3 / 4 : ℝ) := by
    nlinarith [sq_nonneg (r - 1 / 2), sq_nonneg (r + 1 / 2), sq_nonneg (r ^ 2 - r/2), sq_nonneg (r - 3 / 4), sq_pos_of_pos (show (0 : ℝ) < (4 : ℝ) by norm_num)]
  nlinarith [sq_nonneg (r - 1 / 2), sq_nonneg (r ^ 2 - 3 / 4), sq_nonneg (4 * r ^ 3 - 1), sq_nonneg ((r - 3 / 4) * (4 * r * r)), sq_nonneg ((r - 3 / 4) * (r + 1 / 4)), sq_nonneg ((4 * r) * (4 * r)), sq_pos_of_pos (show (0 : ℝ) < (4 : ℝ) by norm_num)]