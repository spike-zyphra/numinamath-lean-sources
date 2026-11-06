import Mathlib

/- Given that the even function $f(x)$ satisfies $f(x+3)=-f(x)$ for any $x∈R$, and $f(x)= \frac {x}{5}$ when $x∈[0,1]$, find the value of $f(107)$.

A: $10$
B: $-10$
C: $ \frac {1}{5}$
D: $- \frac {1}{5}$ -/
theorem algebra_376983 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x, f (x + 3) = -f x) (h₂ : ∀ x ∈ Set.Icc 0 1, f x = x / 5) :
    f 107 = 1 / 5 := by
  have H (x : ℝ) : f (x + 6) = f x := by
    calc f (x + 6)
      _ = f (x + 3 + 3) := by ring_nf
      _ = -f (x + 3) := by rw [h₁]
      _ = f x := by simp [h₁]
  replace H (x : ℝ) (n : ℕ) : f (x + 6 * n) = f x := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc f (x + 6 * (n + 1 : ℕ))
        _ = f (x + 6 * n + 6) := by simp; ring_nf
        _ = f (x + 6 * n) := H _
        _ = f x := ih
  specialize H (-1) 18
  norm_num at H
  rw [H, h₀]
  norm_num [h₂]
