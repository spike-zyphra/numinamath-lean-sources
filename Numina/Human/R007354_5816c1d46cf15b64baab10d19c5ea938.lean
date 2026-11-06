import Mathlib

/- Camila writes down five positive integers.
The unique mode of these integers is $2$ greater than their median, and the median is $2$ greater than their arithmetic mean.
What is the least possible value for the mode?
$\textbf{(A)}\ 5 \qquad\textbf{(B)}\ 7 \qquad\textbf{(C)}\ 9 \qquad\textbf{(D)}\ 11 \qquad\textbf{(E)}\ 13$ -/
theorem algebra_93859 (a b c d e : ℕ) (ha : 0 < a)
    (hmode: e = d)
    (hmedian: d = c + 2 ∧ b < c ∧ a < b) (hmean: (a + b + c + d + e) + 10 = 5 * c): 11 ≤ d := by
    -- trying to find a formula for the median
    have ⟨ hdc, ⟨ hbc ,  hab⟩ ⟩ := hmedian
    rw [hdc]
    rw [hmode, hdc] at hmean
    ring_nf at hmean
    -- Simplifying to prove that the minmum value of the mode is 11
    linarith