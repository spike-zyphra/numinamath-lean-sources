import Mathlib

theorem algebra_276354 (t : ℕ → ℤ) (ht1 : t 1 = 14) (htk : ∀ k ≥ 2, t k = 24 - 5 * t (k - 1))
    (p q r : ℤ) (hpos : ∀ n > 0, t n = p * q ^ n + r) :
    p + q + r = -3 := by
  have eq1 := hpos 1 (by norm_num)
  rw [ht1] at eq1
  have eq2 := hpos 2 (by norm_num)
  have ht2 : t 2 = 24 - 5 * t 1 := htk 2 (by norm_num)
  rw [ht2, ht1] at eq2
  have ht2' : t 2 = -46 := by
    have ht2 : t 2 = 24 - 5 * t 1 := htk 2 (by norm_num)
    rw [ht2, ht1]
    norm_num
  have eq3 := hpos 3 (by norm_num)
  have ht3 : t 3 = 24 - 5 * t 2 := htk 3 (by norm_num)
  rw [ht3, ht2'] at eq3
  norm_num at eq1 eq2 eq3
  have h2 : q = -5 := by
    nlinarith [sq_nonneg (q + 5), sq_nonneg (q - 1)]
  have h1 : p = -2 := by
    rw [h2] at eq1 eq2
    nlinarith
  have h3 : r = 4 := by
    rw [h1, h2] at eq1
    nlinarith
  linarith [h1, h2, h3]