import Mathlib


/- Let $a_{0}=\frac{6}{7}$, and

$$
a_{n+1}= \begin{cases}2 a_{n} & \text { if } a_{n}<\frac{1}{2} \\ 2 a_{n}-1 & \text { if } a_{n} \geq \frac{1}{2}\end{cases}
$$

Find $a_{2008}$. -/
theorem algebra_608426
    (a : ℕ → ℚ)
    (ha0 : a 0 = 6 / 7)
    (ha_lthalf : ∀ n, a n < 1 / 2 → a (n + 1) = 2 * a n)
    (ha_gehalf : ∀ n, 1 / 2 ≤ a n → a (n + 1) = 2 * a n - 1) :
    a 2008 = 5 / 7 := by

  -- We calculate the first few $a_{i}$ :

  -- $a_{1}=\frac{5}{7}$
  have ha1 : a 1 = 5 / 7 := by
    norm_num [ha_gehalf 0 (by norm_num [ha0]), ha0]

  -- $a_{2}=\frac{3}{7}$
  have ha2 : a 2 = 3 / 7 := by
    norm_num [ha_gehalf 1 (by norm_num [ha1]), ha1]

  -- $a_{3}=\frac{6}{7}=a_{0}$
  have ha3 : a 3 = a 0 := by
    norm_num [ha_lthalf 2 (by norm_num [ha2]), ha2, ha0]

  -- So this sequence repeats every three terms
  have : ∀ t, a (3 * t) = a 0 := by
    intro t
    induction t with
    | zero =>
      rfl
    | succ t ih =>
      have t1 : a (3 * t + 1) = a 1 := by
        norm_num [ha_gehalf (3 * t) (by norm_num [ih, ha0]), ih, ha0, ha1]
      have t2 : a (3 * t + 2) = a 2 := by
        norm_num [ha_gehalf (3 * t + 1) (by norm_num [t1, ha1]), t1, ha1, ha2]
      rw [mul_add, mul_one]
      norm_num [ha_lthalf (3 * t + 2) (by norm_num [t2, ha2]), ha0, t2, ha2]

  -- so $a_{2007}=a_{0}=\frac{6}{7}$.
  have : a 2007 = 6 / 7 := by
    rw [← ha0]
    apply this 669

  -- Then $a_{2008}=\frac{5}{7}$.
  norm_num [ha_gehalf 2007 (by norm_num [this]), this]
