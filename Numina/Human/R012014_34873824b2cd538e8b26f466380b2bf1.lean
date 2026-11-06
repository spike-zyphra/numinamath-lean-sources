import Mathlib

/- 11. (20 points) The sequences $\left\{a_{n}\right\}$ and $\left\{b_{n}\right\}$ satisfy:
$$
\begin{array}{l}
a_{1}=1, b_{1}=2, \\
a_{n+1}=\frac{1+a_{n}+a_{n} b_{n}}{b_{n}}, b_{n+1}=\frac{1+b_{n}+a_{n} b_{n}}{a_{n}} .
\end{array}
$$

Compare $a_{2019}$ with 5, and prove your conclusion. -/
theorem algebra_169204 {a b : ℕ → ℝ}
    (ha1 : a 1 = 1) (hb1 : b 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = (1 + a n + a n * b n) / b n)
    (hbn : ∀ n ≥ 1, b (n + 1) = (1 + b n + a n * b n) / a n) :
    a 2019 < 5 := by
  -- We prove that `a n` and `b n` are positive for all `n ≥ 1`
  have habpos : ∀ n ≥ 1, 0 < a n ∧ 0 < b n := by
    intro n hn
    -- Simple induction
    induction n, hn using Nat.le_induction with
    | base => simp [ha1, hb1]
    | succ n hn ih =>
      rcases ih with ⟨ha, hb⟩
      rw [han n hn, hbn n hn]
      constructor <;> positivity
  -- We prove that `1 / (a (n + 1) + 1) = b n / ((1 + a n) * (1 + b n))`
  have H₁ (n : ℕ) (hn : n ≥ 1) : 1 / (a (n + 1) + 1) = b n / ((1 + a n) * (1 + b n)) := by
    have h₁ := (habpos n hn).1
    have h₂ := (habpos n hn).2
    have h₃ := (habpos (n + 1) (by linarith)).1
    specialize han n hn
    -- Cancel the denominators
    field_simp at han ⊢
    linarith only [han]
  -- The same proof works for `b`
  have H₂ (n : ℕ) (hn : n ≥ 1) : 1 / (b (n + 1) + 1) = a n / ((1 + b n) * (1 + a n)) := by
    have h₁ := (habpos n hn).1
    have h₂ := (habpos n hn).2
    have h₃ := (habpos (n + 1) (by linarith)).2
    specialize hbn n hn
    field_simp at hbn ⊢
    linarith only [hbn]
  -- We subtract the two equations, we get `1 / (a (n + 1) + 1) - 1 / (b (n + 1) + 1) = 1 / (a n + 1) - 1 / (b n + 1)`
  have H₃ (n : ℕ) (hn : n ≥ 1) : 1 / (a (n + 1) + 1) - 1 / (b (n + 1) + 1) = 1 / (a n + 1) - 1 / (b n + 1) := by
    rw [H₁ n hn, H₂ n hn]
    have h₁ := (habpos n hn).1
    have h₂ := (habpos n hn).2
    have h₃ := (habpos (n + 1) (by linarith)).1
    have h₄ := (habpos (n + 1) (by linarith)).2
    field_simp
    ring
  -- So we have `1 / (a n + 1) - 1 / (b n + 1) = 1 / (a 1 + 1) - 1 / (b 1 + 1) = 1 / 6` for all `n ≥ 1` by induction
  have H₄ (n : ℕ) (hn : n ≥ 1) : 1 / (a n + 1) - 1 / (b n + 1) = 1 / 6 := by
    induction n, hn using Nat.le_induction with
    | base => norm_num [ha1, hb1]
    | succ n hn ih => rw [H₃ n hn, ih]
  -- We take `n = 2019`, and the result follows
  specialize H₄ 2019 (by simp)
  replace H₄ : 1 / 6 < 1 / (a 2019 + 1) := by
    have h₁ := (habpos 2019 (by simp)).2
    linarith [show 0 < 1 / (b 2019 + 1) by positivity]
  apply lt_of_one_div_lt_one_div (by simp) at H₄
  linarith only [H₄]
