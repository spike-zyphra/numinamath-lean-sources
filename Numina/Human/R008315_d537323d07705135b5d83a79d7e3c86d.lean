import Mathlib

/- Example 1 The sequences $\left\{a_{n}\right\}$ and $\left\{b_{n}\right\}$ satisfy

$$

\begin{array}{l}
a_{0}=b_{0}=1, \\
a_{n+1}=\alpha a_{n}+\beta b_{n}, \\
b_{n+1}=\beta a_{n}+\gamma b_{n},
\end{array}

$$


where $\alpha, \beta, \gamma \in \mathbf{Z}_{+}, \alpha<\gamma$, and $\alpha \gamma=\beta^{2}+1$.
Prove: For any $m, n \in \mathbf{N}$, we have

$$

a_{m+n}+b_{m+n}=a_{m} a_{n}+b_{m} b_{n} \text {. }

$$
 -/
theorem algebra_290954 (α β γ : ℕ) (h₀ : α > 0) (h₁ : β > 0) (h₂ : γ > 0)
    (h₃ : α < γ) (h₄ : α * γ = β ^ 2 + 1) (a b : ℕ → ℤ)
    (ha₀ : a 0 = 1) (hb₀ : b 0 = 1)
    (han : ∀ n, a (n + 1) = α * a n + β * b n)
    (hbn : ∀ n, b (n + 1) = β * a n + γ * b n) :
    ∀ m n, a (m + n) + b (m + n) = a m * a n + b m * b n := by
    intro m n
    -- We prove the more general case from (m + n) to (m + n - k), then set k = m
    suffices h : ∀ k, k ≤ m + n → a (m + n) + b (m + n)
      = a k * a (m + n - k) + b k * b (m + n - k)
    · convert h m _ <;> omega

    intro k kh
    -- We do induction
    induction' k with p n2
    -- k = 0 is trivial
    · simp only [ha₀, tsub_zero, one_mul, hb₀]
    -- induction is a series of equalities
    · calc a (m + n) + b (m + n)
      -- induction hypothesis
      _ = a p * a (m + n - p) + b p * b (m + n - p) := n2 (by omega)
      -- given equalities
      _ = a p * (α * a (m + n - p - 1) + β * b (m + n - p - 1))
        + b p * (β * a (m + n - p - 1) + γ * b (m + n - p - 1)) := by
        have mnp_eq : m + n - p - 1 + 1 = m + n - p := by omega
        congr
        exact (mnp_eq ▸ han (m + n - p - 1))
        exact (mnp_eq ▸ hbn (m + n - p - 1))
      -- factorize
      _ = (α * a p + β * b p) * a (m + n - p - 1)
        + (β * a p + γ * b p) * b (m + n - p - 1) := by ring_nf
      -- given equalities, reverse. We're done.
      _ = a (p + 1) * a (m + n - (p + 1)) + b (p + 1) * b (m + n - (p + 1)) := by
        congr 2
        · exact han p |> Eq.symm
        · exact hbn p |> Eq.symm