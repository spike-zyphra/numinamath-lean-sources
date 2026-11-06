import Mathlib

theorem algebra_120714 (f : ℕ → ℕ) (g : ℕ → ℕ) (h₀ : ∀ n, f n = 2 * n + 1)
    (h₁ : g 1 = 3) (h₂ : ∀ n, g (n + 1) = f (g n)) :
    ∀ n, g n = 2 ^ (n + 1) - 1 := by
  have h3 : g 0 = 1 := by
    have eq1 : g 1 = f (g 0) := h₂ 0
    rw [h₀ (g 0)] at eq1
    rw [h₁] at eq1
    omega
  intro n
  induction n with
  | zero =>
    exact h3
  | succ n ih =>
    have eq1 : g (n + 1) = f (g n) := h₂ n
    rw [eq1]
    rw [h₀ (g n)]
    rw [ih]
    cases n with
    | zero =>
      simp [h₀, h₁, h3]
      <;> omega
    | succ n =>
      simp [pow_succ, pow_zero, h₀, h₁, h₂, h3] at *
      <;> ring_nf at *
      <;> omega