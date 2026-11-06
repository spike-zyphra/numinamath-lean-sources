import Mathlib

theorem algebra_307381 {f : ℝ → ℝ} (hf : f = fun x => x ^ 2 + x - 1)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hne : a * b ^ 2 ≠ 1)
    (h1 : f (a ^ (-1 : ℤ)) = 0) (h2 : f (b ^ 2) = 0) :
    a / (1 + a * b ^ 2) = -1 := by
  have h3 : a ^ (-1 : ℤ) = 1 / a := by
    simp [zpow_neg_one, ha]

  rw [h3] at h1
  have eq1 : (1 / a) ^ 2 + (1 / a) - 1 = 0 := by
    rw [hf] at h1
    simpa using h1

  have eq2 : (b ^ 2) ^ 2 + (b ^ 2) - 1 = 0 := by
    rw [hf] at h2
    simpa using h2

  have eq7 : (1 / a - b ^ 2) * (1 / a + b ^ 2 + 1) = 0 := by
    nlinarith [eq1, eq2]

  cases' (mul_eq_zero.1 eq7) with h10 h11
  · -- Case where $(1 / a - b ^ 2) = 0$.
    have h12 : 1 / a = b ^ 2 := by
      linarith
    have h15 : a * b ^ 2 = 1 := by
      field_simp [ha] at h12 ⊢
      nlinarith
    -- This contradicts hne : a * b ^ 2 ≠ 1
    exfalso
    exact hne (by linarith)
  · -- Case where $1 / a + b ^ 2 + 1 = 0$.
    have h12 : 1 / a + b ^ 2 + 1 = 0 := by
      nlinarith
    have eq8 : 1 + a * b ^ 2 = -a := by
      have h4 : a ≠ 0 := ha
      field_simp at h12 ⊢
      nlinarith
    have eq9 : a / (1 + a * b ^ 2) = -1 := by
      rw [show 1 + a * b ^ 2 = -a by linarith [eq8]]
      have h4 : a ≠ 0 := ha
      field_simp
    exact eq9