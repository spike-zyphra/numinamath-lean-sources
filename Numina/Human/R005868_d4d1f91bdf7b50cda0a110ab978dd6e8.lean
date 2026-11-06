import Mathlib

/- Integers $0 \leq a, b, c, d \leq 9$ satisfy

$$
\begin{gathered}
6 a+9 b+3 c+d=88 \\
a-b+c-d=-6 \\
a-9 b+3 c-d=-46
\end{gathered}
$$

Find $1000 a+100 b+10 c+d$.-/
theorem algebra_610364 (a b c d : ℤ) (ha : 0 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) (hc : 0 ≤ c ∧ c ≤ 9) (hd : 0 ≤ d ∧ d ≤ 9) (h₀ : 6 * a + 9 * b + 3 * c + d = 88) (h₁ : a - b + c - d = -6) (h₂ : a - 9 * b + 3 * c - d = -46) :
    1000 * a + 100 * b + 10 * c + d = 6507 := by
  -- Show that 7a + 6c = 42 by h₀ + h₂.
  have h₃ : 7 * a + 6 * c = 42 := by
    linarith
  -- Show that 4b - c = 20 by (h₁ - h₂) / 2.
  have h₄ : 4 * b - c = 20 := by
    linarith
  -- Since 7a + 6c = 42, either a = 0 or c = 0.
  have h₅ : a = 0 ∨ c = 0 := by
    omega
  cases h₅ with
  | inl h₅ =>
    -- If a = 0, contradictory to h₄.
    omega
  | inr h₅ =>
    -- If c = 0, we have a = 6, b = 5 and d = 7.
    have h₆ : a = 6 := by
      linarith
    have h₇ : b = 5 := by
      linarith
    have h₈ : d = 7 := by
      linarith
    norm_num [h₅, h₆, h₇, h₈]
