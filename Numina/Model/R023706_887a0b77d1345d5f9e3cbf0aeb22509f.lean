import Mathlib

theorem algebra_127712 (a : ℕ → ℝ) (h : ∃ d, ∀ n, a n = a 0 + d * n)
    (ha4 : a 4 + a 7 + a 10 = 17) (hsum : ∑ i in Finset.Icc 4 14, a i = 77)
    (hk : a k = 13) :
    k = 18 := by
  rcases h with ⟨d, had⟩
  have eq1 : a 4 + a 7 + a 10 = 3 * a 0 + 21 * d := by
    rw [had 4, had 7, had 10]
    ring
  rw [eq1] at ha4
  have hsum_eq : ∑ i in Finset.Icc 4 14, a i = 11 * a 0 + 99 * d := by
    simp [Finset.sum_Icc_succ_top, had 4, had 5, had 6, had 7, had 8, had 9, had 10, had 11, had 12, had 13, had 14]
    ring
  rw [hsum_eq] at hsum
  have eq2 : a 0 + 7 * d = 17 / 3 := by
    linarith
  have eq3 : a 0 + 9 * d = 7 := by
    linarith
  have h1 : d = 2 / 3 := by
    linarith
  have h2 : a 0 = 1 := by
    nlinarith
  have eq3 : a k = a 0 + (d * (k : ℝ)) := by
    specialize had k
    simpa using had
  rw [eq3] at hk
  rw [h2, h1] at hk
  have hk_eq : (k : ℝ) = 18 := by
    have h_eq : (k : ℝ) = 18 := by
      linarith
    exact h_eq
  have hk_nat : k = 18 := by
    exact_mod_cast hk_eq
  exact_mod_cast hk_nat