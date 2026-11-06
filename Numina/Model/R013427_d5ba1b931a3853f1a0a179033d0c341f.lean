import Mathlib

/- Let $a$ and $b$ be positive real numbers such that $\frac{a}{1+a}+\frac{b}{1+b}=1$. Show that then

$$
\frac{a}{1+b^{2}}-\frac{b}{1+a^{2}}=a-b
$$

Binomial Theorem: Let us now generalize the other two identities. Let $n$ and $k \leqslant n$ be natural numbers. We denote $\binom{n}{k}$ (pronounced " $k$ out of $n$ ") the number of ways to choose a subset of $k$ elements from a set of $n$ elements. These are the coefficients that will appear in the expansion of $(a+b)^{n}$. More precisely,

Proposition 2.3. (Binomial Theorem) For all $a, b$, we have

$$
(a+b)^{n}=\sum_{k=0}^{n}\binom{n}{k} a^{k} b^{n-k}
$$

Indeed, each term in the expansion of $(a+b)^{n}$ is obtained by choosing $a$ in some factors and $b$ in all the others. Each term is therefore of the form $a^{k} b^{n-k}$ for some $k$. For a fixed $k$, a term $a^{k} b^{n-k}$ is obtained as many times as there are ways to choose $a$ $k$ times from the $n$ factors, which is $\binom{n}{k}$. The coefficient in front of $a^{k} b^{n-k}$ is therefore indeed $\binom{n}{k}$.

However, until we have given a formula for $\binom{n}{k}$, this result does not say much. We actually have the following formula:

Proposition 2.4. Let $n$ be a natural number, and $k$ a natural number less than $n$. Then

$$
\binom{n}{k}=\frac{n!}{k!(n-k)!}=\frac{n(n-1) \ldots(n-k+1)}{k!}
$$

Proof. We will prove the second formula (which is clearly equivalent to the first). The numerator $n(n-1) \ldots(n-k+1)$ corresponds to choosing a first element, for which there are $n$ choices, then a second from the remaining $n-1$ (which gives $(n-1)$ choices), and so on until the $k$-th, for which there are $n-(k-1)=n-k$ choices. Now, the subset obtained does not depend on the order in which its elements were chosen. Therefore, we must divide by the number of permutations of a set of $k$ elements, which is $k!$. -/
theorem algebra_120700 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a / (1 + a) + b / (1 + b) = 1) :
    a / (1 + b ^ 2) - b / (1 + a ^ 2) = a - b := by

  have h1 : a * b = 1 := by 
    have h1 : 0 < (1 + a) * (1 + b) := by positivity
    field_simp [(show 1 + a ≠ 0 by linarith), (show 1 + b ≠ 0 by linarith)] at h
    nlinarith [sq_nonneg (a * b - 1)]

  field_simp [(show 1 + b ^ 2 ≠ 0 by nlinarith), (show 1 + a ^ 2 ≠ 0 by nlinarith)]
  nlinarith [sq_nonneg (a ^ 2 * b ^ 2 - 1), sq_nonneg (a * b - 1), h1, sq_nonneg (a - b), sq_nonneg (a + b), sq_pos_of_pos ha, sq_pos_of_pos hb
]