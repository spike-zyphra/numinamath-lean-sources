import Mathlib

/- Given a sequence of positive terms ${a_n}$ that satisfies $a_1=1$, $a_n-a_{n+1}=a_n \\cdot a_{n+1}$, find the value of $a_{10}$ (Options: A: $\\frac {1}{10}$, B: 10, C: $\\frac {1}{9}$, D: 9) -/
theorem algebra_443050 (a : ℕ → ℝ) (ha : ∀ n > 0, 0 < a n) (h1 : a 1 = 1)
    (h2 : ∀ n > 0, a n - a (n + 1) = a n * a (n + 1)) :
    a 10 = 1 / 10 := by
  have H n (hn : n > 0) : a n = 1 / n := by
    induction n, hn using Nat.le_induction with
    | base =>
      simp [h1]
    | succ n hn ih =>
      have h3 : a (n + 1) = a n / (a n + 1) := by
        field_simp [show a n + 1 ≠ 0 by linarith only [ha n hn]]
        linarith only [h2 n hn]
      rw [h3, ih]
      field_simp
      ring
  norm_num [H]
