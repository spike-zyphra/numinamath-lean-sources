import Mathlib

theorem algebra_303406 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + x) :
    ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 4 * f a = f b := by
  rintro ⟨a, b, ha, hb, heq⟩
  have h1 : (4 * f (a : ℝ) : ℝ) = f (b : ℝ) := by simpa using heq
  simp [hf] at h1
  have h2 : (2 * (a : ℝ) + 1) ^ 2 = (b : ℝ) ^ 2 + (b : ℝ) + 1 := by 
    nlinarith
  have h3 : (2 * a + 1 : ℝ) ^ 2 = (b : ℝ) ^ 2 + (b : ℝ) + 1 := by
    ring_nf at h2 ⊢
    linarith
  have h4 : (2 * a + 1 : ℤ) ^ 2 = (b : ℤ) ^ 2 + (b : ℤ) + 1 := by
    exact_mod_cast h3
  have h5 : (b : ℤ) < (2 * a + 1 : ℤ) := by
    nlinarith [sq_nonneg ((2 * a + 1 : ℤ) : ℤ), sq_nonneg ((b : ℤ) : ℤ), 
      show (2 * a + 1 : ℤ) ^ 2 = (b : ℤ) ^ 2 + (b : ℤ) + 1 by linarith [h4]]
  have h6 : (2 * a + 1 : ℤ) < (b + 1 : ℤ) := by
    nlinarith [sq_nonneg ((2 * a + 1 : ℤ) : ℤ), sq_nonneg ((b : ℤ) : ℤ), 
      show (2 * a + 1 : ℤ) ^ 2 = (b : ℤ) ^ 2 + (b : ℤ) + 1 by linarith [h4]]
  omega