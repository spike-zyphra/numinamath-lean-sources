import Mathlib

/- Let $P(x)$ be a cubic polynomial such that $P(0) = -3$ and $P(1) = 4.$  When $P(x)$ is divided by $x^2 + x + 1,$ the remainder is $2x - 1.$  What is the quotient when $P(x)$ is divided by $x^2 + x + 1$? -/
theorem algebra_20692 {P : ℝ → ℝ} (a b c d :ℝ) (hP : ∃ a b c d, P = fun x => a*x^3 + b*x^2 + c*x + d)
    (hP0 : P 0 = -3) (hP1 : P 1 = 4) (hP2 : ∃ e f, ∀ x : ℝ, P x = (e * x + f) * (x ^ 2 + x + 1) + 2 * x - 1) (hP3 : ∀ x : ℝ, P x = (a * x + b) * (x ^ 2 + x + 1) + c * x + d) : a = 3 ∧ b = -2 := by
    -- introduce e, f
    rcases hP2 with ⟨e, f, hP2⟩
    --solve for e, f
    have hf : f = -2 := by
        -- substitute x = 0
        specialize hP2 0
        -- use hP0
        rw [hP0] at hP2
        ring_nf at hP2
        linarith
    have he : e = 3 := by
        -- substitute x = 1
        specialize hP2 1
        -- use hP1
        rw [hP1] at hP2
        ring_nf at hP2
        linarith
    -- substitute e, f
    rw [hf, he] at hP2
    -- simplify the expression for P(x)
    ring_nf at hP2
    -- rewrite hP3
    replace hP3 : ∀ x, -3 + x * 3 + x ^ 2 + x ^ 3 * 3 = (a * x + b) * (x ^ 2 + x + 1) + c * x + d := by
        intro x
        specialize hP3 x
        specialize hP2 x
        rw [←hP3, ←hP2]
    -- solve for a, b
    -- eqution 1: d = - b - 3
    have heq1 : d = - b - 3 := by
        -- substitute x = 0
        specialize hP3 0
        ring_nf at hP3
        linarith
    -- equation 2: c = - a + 5
    have heq2 : c = - a + 5 := by
        -- substitute x = 1
        specialize hP3 (-1 : ℝ)
        ring_nf at hP3
        linarith
    -- equation 3: a + b = 1
    have heq3 : a + b = 1 := by
        -- substitute x = 1
        specialize hP3 1
        ring_nf at hP3
        rw [heq1, heq2] at hP3
        ring_nf at hP3
        linarith
    -- substitute x = 2
    specialize hP3 2
    -- solve for a, b
    rw [heq1, heq2] at hP3
    ring_nf at hP3
    -- trivial solution
    have ha : a = 3 := by
        linarith
    have hb : b = -2 := by
        linarith
    exact ⟨ha, hb⟩
