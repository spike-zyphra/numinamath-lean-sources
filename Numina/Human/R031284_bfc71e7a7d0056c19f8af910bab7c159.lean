import Mathlib

open Real Set
open scoped BigOperators

/- The inverse function of $y= \begin{cases} x, & x<0 \\ x^{2}, & x\geq 0 \end{cases}$ is _____________. -/
theorem algebra_9314 {f g : ℝ → ℝ} (hf : f = λ x => if x < 0 then x else x^2) (hg : g = λ x => if x < 0 then x else sqrt x) : Function.LeftInverse g f ∧ Function.RightInverse g f := by
-- we show g is the inverse function of f by showing g is both left inverse and right inverse.
have left: (g ∘ f)  = id := by
  ext x
  rw [hf, hg]
  simp
  by_cases hx : x < 0
  -- when x<0, f(x)=x, g(x)=x, g ∘ f = id ∘ id.
  repeat rw [if_pos hx]
  -- when x ≥ 0, f(x)=x^2, g(x) = √x, (g ∘ f) (x)= √(x^2) = x.
  rw [if_neg hx]
  have h2: ¬ x^2 < 0 := by
    have: 0 ≤ x^2 := sq_nonneg x
    linarith [this]
  rw [if_neg h2]
  have hx' : 0 ≤ x := by linarith [hx]
  exact Real.sqrt_sq hx'
have right: (f ∘ g) = id := by
    ext x
    rw [hf, hg]
    simp
    by_cases hx: x < 0
    -- when x<0, g(x) = x, f(x)=x, f ∘ g = id ∘ id
    repeat rw [if_pos hx]
    -- when x ≥ 0, g(x) = √x, f(x) = x^2, (f ∘ g)(x) = (√x)^2 = x
    repeat rw [if_neg hx]
    push_neg at hx
    have h1: ¬ √x < 0 := by
        by_contra! hc
        have: 0 ≤ √x := sqrt_nonneg x
        linarith [this, hc]
    rw [if_neg h1]
    exact sq_sqrt hx
exact ⟨congrFun left, congrFun right⟩