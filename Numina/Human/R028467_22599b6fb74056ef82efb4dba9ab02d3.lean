import Mathlib
/- Let $P(x)$ be a quadratic polynomial with real coefficients. Suppose that $P(1)=20, P(-1)=22$, and $P(P(0))=400$. Compute the largest possible value of $P(10)$. -/
theorem algebra_610513 : IsGreatest {S : ℝ | ∃ a b c : ℝ, ∃ P : ℝ → ℝ, (P = fun x => a * x ^ 2 + b * x + c) ∧ P 1 = 20 ∧ P (-1) = 22 ∧ P (P 0) = 400 ∧ S = P 10} 2486:= by
  constructor
  .
    simp
    use 25, -1, -4
    norm_num
  .
    simp [upperBounds]
    intro S a b c h1 h2 h3 hS
    subst S
    replace h2 : b = -1:= by linarith
    replace h1 : a = 21 - c:= by linarith
    subst a b
    replace h3 : (c + 4) * (c - 5) * (c - 20) = 0:= by linarith
    simp at h3
    rcases h3 with ⟨h3 | h3⟩ | h3
    .
      replace h3 : c = -4:= by linarith
      subst c
      linarith
    .
      replace h3 : c = 5:= by linarith
      subst c
      linarith
    .
      replace h3 : c = 20:= by linarith
      subst c
      linarith

