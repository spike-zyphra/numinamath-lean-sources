import Mathlib

/- If $f(x) = x^2 + x$, prove that the equation $4f(a) = f(b)$ has no solutions in positive integers $a$ and $b$. -/
theorem algebra_52507 {f : ℤ → ℤ} (hf : ∀ x, f x = x ^ 2 + x) :
    ¬∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 4 * f a = f b := by 
  rintro ⟨a, b, ha : 0 < a, hb : 0 < b, hf₁⟩
  simp only [hf] at hf₁
  ring_nf at hf₁
  norm_cast at hf₁
  ring_nf at hf₁
  have h₁ : 4 * a ^ 2 + 4 * a = b ^ 2 + b := by linarith
  have h₂ : 2 * a + 1 ≤ b := by nlinarith
  have h₃ : b ≤ 2 * a + 1 := by nlinarith
  have h₄ : b = 2 * a + 1 := by linarith
  rw [h₄] at hf₁
  linarith