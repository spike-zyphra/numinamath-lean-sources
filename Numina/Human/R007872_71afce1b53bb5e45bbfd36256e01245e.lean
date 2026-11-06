import Mathlib

/- Each letter represents a non-zero digit. What is the value of $t?$ \begin{align*}
c + o &= u \\
u + n &= t \\
t + c &= s \\
o + n + s &= 12
\end{align*} -/
theorem algebra_16399 (c o u n t s : ℕ) (hc : c > 0 ∧ c < 10) (ho : o > 0 ∧ o < 10)
    (hu : u > 0 ∧ u < 10) (hn : n > 0 ∧ n < 10) (ht : t > 0 ∧ t < 10) (hs : s > 0 ∧ s < 10)
    (h1 : c + o = u) (h2 : u + n = t) (h3 : t + c = s) (h4 : o + n + s = 12) : t = 6 := by
  omega
