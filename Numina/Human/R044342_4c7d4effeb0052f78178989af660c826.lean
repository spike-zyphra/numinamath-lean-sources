import Mathlib

/- Soit $a$ et $b$ des entiers strictement positifs. Prouver que si

$$
a+\frac{b}{a}-\frac{1}{b}
$$

est un entier alors c'est un carré. -/
theorem number_theory_605199 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : ∃ n : ℤ, (a + b / a - 1 / b : ℚ) = n) :
    ∃ m : ℤ, (a + b / a - 1 / b : ℚ) = m^2 := by
  rcases h₁ with ⟨n, hn⟩
  -- By multiplying by a, we obtain that a ^ 2 + b - a / b = a * n is an integer.
  -- So a / b = a ^ 2 + b - a * n is an integer, say k.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (a / b : ℚ) = k := by
    use a ^ 2 + b - a * n
    simp
    field_simp [← hn]
    ring
  -- k is positive.
  have kpos : k > 0 := by
    qify
    rw [← hk]
    positivity
  -- By multiplying by b, we obtain that a * b + b ^ 2 / a - 1 = b * n is an integer.
  -- So b / k = b ^ 2 / a = b * n + 1 - a * b is an integer, say c.
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (b / k : ℚ) = c := by
    use b * n + 1 - a * b
    simp
    field_simp [← hk, ← hn]
    ring
  -- c is positive.
  have cpos : c > 0 := by
    qify
    rw [← hc]
    positivity
  -- a + b / a - 1 / b = a + 1 / k - 1 / (k * c) = n is an integer.
  -- So 1 / c = 1 - (n - a) * k is an integer, say s.
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (1 / c : ℚ) = s := by
    use 1 - (n - a) * k
    simp
    field_simp [← hc, ← hn, ← hk]
    ring
  -- We have c * s = 1.
  replace hs : c * s = 1 := by
    qify at cpos ⊢
    field_simp [← hs]
  -- So c = 1.
  obtain rfl : c = 1 := Int.eq_one_of_mul_eq_one_right (le_of_lt cpos) hs
  -- So b = k.
  obtain rfl : k = b := by
    field_simp at hc
    exact hc.symm
  -- So a = k ^ 2.
  obtain rfl : a = k ^ 2 := by
    field_simp at hk
    qify
    linear_combination hk
  -- And a + b / a - 1 / b = k ^ 2.
  use k
  field_simp
  ring
