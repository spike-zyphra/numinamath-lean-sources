import Mathlib

/- Let $a$,$b$,$c$,$d$, and $e$ be five consecutive terms in an arithmetic sequence, and suppose that $a+b+c+d+e=30$.  Which of the following can be found? $$\text{(A)}\ a \qquad \text{(B)}\ b \qquad \text{(C)}\ c \qquad \text{(D)}\ d \qquad \text{(E)}\ e $$Enter the letter of the correct option, so your answer will be A, B, C, D, or E. -/
theorem algebra_21181 {a b c d e : ℤ} (h : ∃ d1, b = a + d1 ∧ c = b + d1 ∧ d = c + d1 ∧ e = d + d1)
    (h' : a + b + c + d + e = 30) : c = 6 := by
        rcases h with ⟨d1, ⟨h1, h2, h3, h4⟩⟩
        linarith