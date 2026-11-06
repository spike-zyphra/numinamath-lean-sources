import Mathlib

/- ## Task A-4.2.

A sequence $\left(a_{n}\right)$ is given such that $a_{0}=1, a_{1}=4$ and


$$

a_{n}=3 a_{n-1}+4 a_{n-2}

$$


for every natural number $n \geqslant 2$.

Prove that all terms of the sequence $\left(a_{n}\right)$ are squares of natural numbers. -/
theorem algebra_216592 {a : ℕ → ℕ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 4)
    (han : ∀ n ≥ 2, a n = 3 * a (n - 1) + 4 * a (n - 2)) :
    ∀ n : ℕ, ∃ m : ℕ, a n = m ^ 2 := by
      --We show that a n = 2^(2 * n) for every n ∈ ℕ by induction.
      have H1 : ∀ n, a n = 2^(2 * n) ∧ a (n + 1) = 2^(2 * (n +1)) := by
        intro n
        induction n with
        |zero =>
        constructor
        exact ha0
        exact ha1
        |succ n ih =>
        constructor
        exact ih.2
        have h1 : n + 2 ≥ 2 := by omega
        have h2 := han (n + 2) h1
        simp at h2
        have ih1 : a n = 2^(2 * n) := by exact ih.1
        have ih2 : a (n + 1) = 2^(2 * (n + 1)) := by exact ih.2
        rw [ih1, ih2] at h2
        have h3 : 3 * 2^(2 * (n + 1)) + 4 * 2^(2 * n) = 2^(2 * (n + 2)) := by ring
        have h4 : a (n + 2) = 2^(2 * (n + 2)) := by linarith
        rw [h4]
      --Therefore for all n ∈ ℕ, a n = 2^(2 * n).
      intro n
      have H2 : a n = 2^(2 * n) := by
        exact (H1 n).1
      have H3 : 2^(2 * n) = (2^n)^2 := by ring
      simp [H3] at H2
      use 2^n