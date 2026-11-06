import Mathlib

open Real Set

/- Let $a, b, c$ be real numbers greater than or equal to 1 . Prove that

$$

\min \left(\frac{10 a^{2}-5 a+1}{b^{2}-5 b+10}, \frac{10 b^{2}-5 b+1}{c^{2}-5 c+10}, \frac{10 c^{2}-5 c+1}{a^{2}-5 a+10}\right) \leq a b c .

$$
 -/
theorem inequalities_245776 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    min (min ((10 * a ^ 2 - 5 * a + 1) / (b ^ 2 - 5 * b + 10)) ((10 * b ^ 2 - 5 * b + 1) / (c ^ 2 - 5 * c + 10))) ((10 * c ^ 2 - 5 * c + 1) / (a ^ 2 - 5 * a + 10)) ≤ a * b * c := by
  -- first we define functions for numerator, denominator and minimum for ease of writing and change the goal
  let f := fun (x : ℝ) ↦ 10 * x^2 - 5 * x + 1
  let g := fun (x : ℝ) ↦ x^2 - 5 * x + 10
  let m := f a / g b ⊓ f b / g c ⊓ f c / g a
  change m ≤ a * b * c
  -- now by expressing the numerator and denominator using sqaure of linear expression, we prove their positivity
  have h₁ (x : ℝ) : 0 < g x := by
    simp [g]
    linarith [show 0 ≤ (x - 5/2)^2 by positivity]
  have h₂ (x : ℝ) : 0 < f x := by
    simp [f]
    linarith [show 0 ≤ (x - 1/4)^2 by positivity]
  -- next we prove for 1 ≤ x, f x / g x ≤ x^3, this is same as the fact 0 ≤ (x-1)^5
  have h₃ {x : ℝ} (h: 1 ≤ x) : f x / g x ≤ x^3 := by
    calc
      f x / g x ≤ x^3 * g x / g x := by
        gcongr
        . linarith [h₁ x]
        . simp [f, g]
          have : 0 ≤ (x - 1)^5 := by
            apply pow_nonneg
            linarith
          linarith
      _ = x^3 := by
        specialize h₁ x
        field_simp
  -- we declare positivity of f,g of a, b, c as that will be used by other tactics
  have := h₁ a
  have := h₁ b
  have := h₁ c
  have := h₂ a
  have := h₂ b
  have := h₂ c
  -- multiplying h₃ for a, b, c we get following inequality
  have h₄ : (f a / g a) * (f b / g b) * (f c / g c) ≤ a^3 * b^3 * c^3 := by
    gcongr
    all_goals exact h₃ (by assumption)
  -- we shift the denominators to get closer to our goal
  replace h₄ : (f a / g b) * (f b / g c) * (f c / g a) ≤ (a * b * c)^3 := by
    linear_combination h₄
  -- next we prove m^3 ≤ lhs of h₄, as m is all of their minimum
  have h₅ : m^3 ≤ (f a / g b) * (f b / g c) * (f c / g a) := by
    rw [show m^3 = m * m * m by ring]
    have : m ≤ f a / g b ⊓ f b / g c := by exact min_le_left _ _
    gcongr
    . have := min_le_left (f a / g b) (f b / g c)
      linarith
    . have := min_le_right (f a / g b) (f b / g c)
      linarith
    . exact min_le_right _ _
  -- now m^3 ≤ (a*b*c)^3, from that we get our goal
  have h₄ : m^3 ≤ (a * b * c)^3 := by linarith
  exact le_of_pow_le_pow_left₀ (show 3 ≠ 0 by norm_num) (by positivity) h₄