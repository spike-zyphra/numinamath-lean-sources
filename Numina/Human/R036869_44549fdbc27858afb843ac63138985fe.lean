import Mathlib
open Mathlib
/-- Given that

\begin{align*}x_{1}&=211,\\ x_{2}&=375,\\ x_{3}&=420,\\ x_{4}&=523,\ \text{and}\\ x_{n}&=x_{n-1}-x_{n-2}+x_{n-3}-x_{n-4}\ \text{when}\ n\geq5, \end{align*}

find the value of $x_{531}+x_{753}+x_{975}$. -/
theorem algebra_97709 (x : ℕ → ℤ)
(h0 : x 0 = 211)
(h1 : x 1 = 375)
(h2 : x 2 = 420)
(h3 : x 3 = 523)
(h4 : ∀ n, x (n + 4) = x (n + 3) - x (n + 2) + x (n + 1) - x n) :
x 530 + x 752 + x 974 = 898 := by
  -- https://artofproblemsolving.com/wiki/index.php/2001_AIME_II_Problems/Problem_3
  /- Summing the recursions

  \begin{align*} x_{n}&=x_{n-1}-x_{n-2}+x_{n-3}-x_{n-4} \\ x_{n-1}&=x_{n-2}-x_{n-3}+x_{n-4}-x_{n-5} \end{align*}

  yields $x_{n} = -x_{n-5}$. -/
  have h5 (n : ℕ) : x (n + 5) = -x n:= by
    have h6 := h4 n
    have h7 := h4 (n + 1)
    simp only [(by intros a b c; ring : ∀ a b c : ℕ, a + b + c = a + (b + c))] at h7
    norm_num at h7
    rw [h6] at h7
    ring_nf at h7
    rw [←h7, add_comm]
  -- Since $531 = 106 ⬝ 5 + 1,\ 753 = 150 \cdot 5 + 3,\ 975 = 194 \cdot 5 + 5$, it follows that
  have s : x 530 = x 0 := by simp only [h5, neg_neg]
  have t : x 752 = x 2 := by simp only [h5, neg_neg]
  have h10 (n : ℕ) : x (n + 10) = x n := by simp only [h5, neg_neg]
  have u : x 974 = x 4 := by simp only [h10, neg_neg]
  -- \[x_{531} + x_{753} + x_{975} = (-1)^{106} x_1 + (-1)^{150} x_3 + (-1)^{194} x_5 = 211 + 420 + 267 = \boxed{898}.\]
  rw [s, t, u, h0, h2, h4, h1, h3, h2, h0]
  norm_num