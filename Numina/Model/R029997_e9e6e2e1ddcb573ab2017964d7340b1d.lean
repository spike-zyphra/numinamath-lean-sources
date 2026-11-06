import Mathlib

theorem algebra_52507 {f : ℤ → ℤ} (hf : ∀ x, f x = x ^ 2 + x) :
    ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 4 * f a = f b := by 
  rintro ⟨a, b, ha : 0 < a, hb : 0 < b, hf₁⟩
  have h1 : 4 * f a = 4 * (a ^ 2 + a) := by 
    rw [hf]
  have h2 : f b = b ^ 2 + b := hf b
  rw [h1, h2] at hf₁
  have h3 : (2 * a + 1 : ℤ) ^ 2 = (b : ℤ) ^ 2 + (b : ℤ) + 1 := by
    ring_nf at hf₁ ⊢
    nlinarith 
  have h4 : (b : ℤ) < (2 * a + 1 : ℤ) := by
    nlinarith [sq_nonneg ((2 * a + 1 : ℤ) - (b : ℤ)), sq_nonneg ((b : ℤ) - (2 * a + 1 : ℤ)), sq_nonneg ((2 * a + 1 + b : ℤ)), sq_nonneg ((b : ℤ) - (2 * a + 1) : ℤ)]
  have h5 : (2 * a + 1 : ℤ) < (b + 1 : ℤ) := by
    nlinarith [sq_nonneg ((2 * a + 1 : ℤ) - (b : ℤ)), sq_nonneg ((b : ℤ) - (2 * a + 1 : ℤ)), sq_nonneg ((2 * a + 1 + b : ℤ)), sq_nonneg ((b : ℤ) - (2 * a + 1) : ℤ)]
  omega