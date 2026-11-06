import Mathlib

open Polynomial
/- 10. Given that
$$
\begin{aligned}
\alpha+\beta+\gamma & =14 \\
\alpha^{2}+\beta^{2}+\gamma^{2} & =84 \\
\alpha^{3}+\beta^{3}+\gamma^{3} & =584
\end{aligned}
$$
find $\max \{\alpha, \beta, \gamma\}$. -/

theorem algebra_100581 (α β γ : ℝ) (h1 : α + β + γ = 14) (h2 : α^2 + β^2 + γ^2 = 84) (h3 : α^3 + β^3 + γ^3 = 584) :
    max (max α β) γ = 8 := by

    -- for simplicity, we simplify the notation
    set a:= α
    set b:= β
    set c:= γ
    clear_value a b c

    -- we show that the "polynomials" are equal
    have h: ∀ x: ℝ, (x - a) * (x - b) * (x - c) - (x ^ 3 - 14 * x ^ 2 + 56 * x - 64) = 0 := by
        intro x
        rw [show (x - a) * (x - b) * (x - c) - (x ^ 3 - 14 * x ^ 2 + 56 * x - 64)
        = -x ^ 2 * (a + b + c - 14) + x * (a * b + a * c + b * c - 56) - (a * b * c - 64) by ring]
        have s1: a + b + c = 14 := by
            rw [h1]
        have s2: a * b + a * c + b * c = 56 := by
            rw [show a * b + a * c + b * c = ((a + b + c)^2 - (a^2 + b^2 + c^2)) / 2 by ring]
            rw [h1,h2]
            norm_num
        have s3: a * b * c = 64 := by
            have eq: a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by
                ring
            rw [h1,h2,h3,s2] at eq
            nlinarith
        simp [s1,s2,s3]

    -- then we specialize h at the roots of the latter polynomial
    have f1:= h 2
    norm_num at f1
    have f2:= h 4
    norm_num at f2
    have f3:= h 8
    norm_num at f3
    replace f1: 2 - a = 0 ∨ 2 - b = 0 ∨ 2 - c = 0 := by tauto
    replace f2: 4 - a = 0 ∨ 4 - b = 0 ∨ 4 - c = 0 := by tauto
    replace f3: 8 - a = 0 ∨ 8 - b = 0 ∨ 8 - c = 0 := by tauto
    rcases f1 with f1 | f1 | f1
    <;> rcases f2 with f2 | f2 | f2
    <;> rcases f3 with f3 | f3 | f3
    all_goals try nlinarith
    .
        replace f1: a = 2 := by linarith
        replace f2: b = 4 := by linarith
        replace f3: c = 8 := by linarith
        simp [f1,f2,f3]
        norm_num
    .
        replace f1: a = 2 := by linarith
        replace f2: b = 8 := by linarith
        replace f3: c = 4 := by linarith
        simp [f1,f2,f3]
        norm_num
    .
        replace f1: a = 4 := by linarith
        replace f2: b = 2 := by linarith
        replace f3: c = 8 := by linarith
        simp [f1,f2,f3]
        norm_num
    .
        replace f1: a = 8 := by linarith
        replace f2: b = 2 := by linarith
        replace f3: c = 4 := by linarith
        simp [f1,f2,f3]
        norm_num
    .
        replace f1: a = 4 := by linarith
        replace f2: b = 8 := by linarith
        replace f3: c = 2 := by linarith
        simp [f1,f2,f3]
        norm_num
    .
        replace f1: a = 8 := by linarith
        replace f2: b = 4 := by linarith
        replace f3: c = 2 := by linarith
        simp [f1,f2,f3]
        norm_num