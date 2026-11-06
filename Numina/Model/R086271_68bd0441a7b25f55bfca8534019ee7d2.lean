import Mathlib

theorem algebra_1094 {m n p q : ℝ} (h₀ : m ≠ n) (h₁ : m ≠ p) (h₂ : m ≠ q)
(h₃ : n ≠ p) (h₄ : n ≠ q) (h₅ : p ≠ q) (h₆ : (n + q) * (n + m) = 1) (h₇ : (p + q) * (p + m) = 1) :
(n + q) * (p + q) = -1 := by
  have eq1 : (n + q) * (n + m) = (p + q) * (p + m) := by
    linarith
  have eq2 : (n - p) * (n + p + m + q) = 0 := by
    linarith [eq1]
  have h₈ : n + p + m + q = 0 := by
    apply_fun (λ x => x / (n - p)) at eq2
    field_simp [(show (n - p) ≠ 0 by intro h; apply h₃; linarith)] at eq2
    linarith
  have ht : (n + q) * (p + q) = -1 := by
    have h₉ : n + q = - (p + m) := by
      nlinarith [h₈]
    rw [h₉]
    nlinarith [h₇]
  exact ht