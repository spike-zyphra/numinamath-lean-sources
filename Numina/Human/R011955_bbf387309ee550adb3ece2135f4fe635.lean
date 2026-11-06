import Mathlib

/- Consider the sequences $\left(a_{n}\right)_{n \geqslant 0}$ and $\left(b_{n}\right)_{n \geqslant 0}$ defined by $a_{0}=1, b_{0}=2$ and for all $n \geqslant 0$ :

$$
\begin{aligned}
& a_{n+1}=\frac{a_{n} b_{n}+a_{n}+1}{b_{n}} \\
& b_{n+1}=\frac{a_{n} b_{n}+b_{n}+1}{a_{n}}
\end{aligned}
$$

Show that $a_{2020}<5$. -/
theorem algebra_162771 {a b : ℕ → ℝ}
    (ha0 : a 0 = 1) (hb0 : b 0 = 2)
    (han : ∀ n, a (n + 1) = (1 + a n + a n * b n) / b n)
    (hbn : ∀ n, b (n + 1) = (1 + b n + a n * b n) / a n) :
    a 2020 < 5 := by
  -- We prove that `a n` and `b n` are positive for all `n ≥ 1`
  have habpos (n : ℕ) : 0 < a n ∧ 0 < b n := by
    -- Simple induction
    induction n with
    | zero => simp [ha0, hb0]
    | succ n ih =>
      rcases ih with ⟨ha, hb⟩
      rw [han n, hbn n]
      constructor <;> positivity
  -- We prove that `1 / (a (n + 1) + 1) = b n / ((1 + a n) * (1 + b n))`
  have H₁ (n : ℕ) : 1 / (a (n + 1) + 1) = b n / ((1 + a n) * (1 + b n)) := by
    have h₁ := (habpos n).1
    have h₂ := (habpos n).2
    have h₃ := (habpos (n + 1)).1
    specialize han n
    -- Cancel the denominators
    field_simp at han ⊢
    linarith only [han]
  -- The same proof works for `b`
  have H₂ (n : ℕ) : 1 / (b (n + 1) + 1) = a n / ((1 + b n) * (1 + a n)) := by
    have h₁ := (habpos n).1
    have h₂ := (habpos n).2
    have h₃ := (habpos (n + 1)).2
    specialize hbn n
    field_simp at hbn ⊢
    linarith only [hbn]
  -- We subtract the two equations, we get `1 / (a (n + 1) + 1) - 1 / (b (n + 1) + 1) = 1 / (a n + 1) - 1 / (b n + 1)`
  have H₃ (n : ℕ) : 1 / (a (n + 1) + 1) - 1 / (b (n + 1) + 1) = 1 / (a n + 1) - 1 / (b n + 1) := by
    rw [H₁ n, H₂ n]
    have h₁ := (habpos n).1
    have h₂ := (habpos n).2
    have h₃ := (habpos (n + 1)).1
    have h₄ := (habpos (n + 1)).2
    field_simp
    ring
  -- So we have `1 / (a n + 1) - 1 / (b n + 1) = 1 / (a 1 + 1) - 1 / (b 1 + 1) = 1 / 6` for all `n` by induction
  have H₄ (n : ℕ) : 1 / (a n + 1) - 1 / (b n + 1) = 1 / 6 := by
    induction n with
    | zero => norm_num [ha0, hb0]
    | succ n ih => rw [H₃ n, ih]
  -- We take `n = 2020`, and the result follows
  specialize H₄ 2020
  replace H₄ : 1 / 6 < 1 / (a 2020 + 1) := by
    have h₁ := (habpos 2020).2
    linarith [show 0 < 1 / (b 2020 + 1) by positivity]
  apply lt_of_one_div_lt_one_div (by simp) at H₄
  linarith only [H₄]
