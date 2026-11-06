import Mathlib

/- Let $p(x)$ be a cubic polynomial such that $p(-3) = -6,$ $p(4) = 8,$ $p(5) = 10,$ and $p(7) = 15.$  Find $p(12).$ -/
theorem algebra_20675 {p : ℝ → ℝ} (hp : ∃ a b c d, a ≠ 0 ∧ p = fun x => a*x^3 + b*x^2 + c*x + d)
    (h1 : p (-3) = -6) (h2 : p 4 = 8) (h3 : p 5 = 10) (h4 : p 7 = 15) :
    p 12 = 38 := by 
  obtain ⟨a,b,c,d,h⟩ := hp
  simp_all
  linarith