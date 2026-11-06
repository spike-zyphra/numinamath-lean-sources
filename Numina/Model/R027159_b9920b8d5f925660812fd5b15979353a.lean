import Mathlib

theorem algebra_264468 {f : ℕ → ℕ} (hf : f = fun x => x ^ 2 + x) :
    ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 4 * f a = f b := by
  rintro ⟨a, b, ha, hb, heq⟩
  simp [hf] at heq
  have eq1 : 4 * (a ^ 2 + a) = b ^ 2 + b := by
    linarith
  have eq2 : (2 * a + 1) ^ 2 = b ^ 2 + b + 1 := by
    nlinarith [eq1]
  have h1 : b ^ 2 < b ^ 2 + b + 1 := by
    nlinarith [hb]
  have h2 : b ^ 2 + b + 1 < (b + 1) ^ 2 := by
    nlinarith [hb]
  have h3 : b < 2 * a + 1 := by
    nlinarith [sq_nonneg (b : ℕ), sq_nonneg (2 * a + 1 : ℕ), sq_nonneg (b - (2 * a + 1 : ℕ)), sq_nonneg ((2 * a + 1 : ℕ) - b), eq2, hb]
  have h4 : 2 * a + 1 < b + 1 := by
    nlinarith [sq_nonneg (b : ℕ), sq_nonneg (2 * a + 1 : ℕ), sq_nonneg (b - (2 * a + 1 : ℕ)), sq_nonneg ((2 * a + 1 : ℕ) - b), eq2, hb]
  omega