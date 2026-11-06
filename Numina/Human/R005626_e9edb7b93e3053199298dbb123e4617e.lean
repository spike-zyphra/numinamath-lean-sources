import Mathlib

/- Evaluate the expression
$$
\frac{1}{2 - \frac{1}{2 - \frac{1}{2 - \cdots \frac{1}{2 - \frac{1}{2}}}}}
$$
where the digit 2 appears 2013 times. -/
theorem algebra_609164
    (f : ℕ → ℚ)
    (hf0 : f 0 = 0)
    (hfn : ∀ n, f (n + 1) = 1 / (2 - f n)) :
    f 2013 = 2013 / 2014 := by

  -- by induction, $f_n = \frac{n}{n+1}.$
  have (n : ℕ) : f n = n / (n + 1) := by
    induction n with
    | zero =>
      norm_num [hf0]
    | succ n ih =>
      convert hfn n using 1
      rw [ih, Nat.cast_add, Nat.cast_one,
          sub_div', show 2 * (n + 1 : ℚ) - n = n + 1 + 1 by ring]
      field_simp
      norm_cast
  -- so $f(2013)=\frac{2013}{2014}$.
  convert this 2013
  norm_num
