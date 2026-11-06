import Mathlib

theorem algebra_313382 :
    (∀ a b c d : ℝ, b ≠ 0 → d ≠ 0 → b + d ≠ 0 →
      a / b = c / d →
       a / b = (a + c) / (b + d)) ∧ ¬ (∀ a b c d : ℝ, b ≠ 0 → d ≠ 0 → b + d ≠ 0 →
      a / b = c / d → a / b = a * c / b * d) := by
  constructor
  · -- Proof of the first statement
    intros a b c d hb hd hbd heq
    -- From the hypothesis $\frac{a}{b} = \frac{c}{d}$, cross-multiplying gives $a \cdot d = b \cdot c$.
    have h1 : a / b = c / d := heq
    have h2 : a * d = b * c := by 
      field_simp [hb, hd] at h1 ⊢
      linarith
    -- To prove $\frac{a}{b} = \frac{a + c}{b + d}$, cross-multiplying gives $a \cdot (b + d) = b \cdot (a + c)$.
    -- Expanding: $a \cdot b + a \cdot d = b \cdot a + b \cdot c$.
    -- Subtract $a \cdot b$ from both sides: $a \cdot d = b \cdot c$, which is `h2`.
    have h3 : a * (b + d) = b * (a + c) := by
      have h4 : a * d = b * c := h2
      linarith
    -- Show $\frac{a}{b} = \frac{a + c}{b + d}$ using h3.
    have h4 : a / b = (a + c) / (b + d) := by 
      field_simp [hb, hd, hbd]
      <;> nlinarith [h3]
    exact h4
  · -- Proof of the second statement (negation)
    intro h
    have h1 := h 1 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1