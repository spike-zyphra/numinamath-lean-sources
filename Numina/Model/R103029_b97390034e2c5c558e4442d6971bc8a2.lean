import Mathlib

def f (n : ℕ) : ℕ := match n with
  | 0 => 1
  | n + 1 => (3 * f n + 1)

theorem number_theory_3639 : f 2016 % 3 = 1 := by
  have h1 : ∀ (n : ℕ), (f n) % 3 = 1 := by
    intro n
    induction n with
    | zero =>
      simp [f]
    | succ n ih =>
      simp [f] at ih ⊢
      omega
  have h2 : (f 2016) % 3 = 1 := h1 2016
  exact h2