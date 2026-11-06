import Mathlib

theorem number_theory_31078 (k : ℤ)
  (a : ℕ → ℤ)
  (h₀ : a 0 = 0)
  (h₁ : a 1 = k)
  (h₂ : ∀ n, a (n + 2) = k^2 * a (n + 1) - a n) :
  ∀ n, (a (n + 1)) * (a n) + 1 ∣ (a (n + 1))^2 + (a n)^2 := by
  intro n
  have h3 : ∀ n, a (n + 1) ^ 2 + a n ^ 2 = k ^ 2 * ( (a (n + 1) ) * (a n) + 1 ) := by
    intro n
    induction n with
    | zero =>
      simp [h₀, h₁]
      <;> nlinarith
    | succ n ih =>
      have eq1 : a (n + 2) = k^2 * a (n + 1) - a n := h₂ n
      simp [eq1] at ih ⊢
      <;> nlinarith [sq_nonneg (a (n + 1) ^ 2), sq_nonneg (a n ^ 2), sq_nonneg (k ^ 2 * a (n + 1) * a n), sq_nonneg (k ^ 2 * a (n + 1) * a n) ]
  specialize h3 n
  use k ^ 2
  all_goals nlinarith