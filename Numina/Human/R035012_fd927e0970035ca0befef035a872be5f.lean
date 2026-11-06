import Mathlib

/- $3$ rational numbers $a$, $b$, $c$ are all distinct from each other, then among $\frac{a-b}{b-c}$, $\frac{b-c}{c-a}$, $\frac{c-a}{a-b}$, there are ___          ___ negative numbers. -/
theorem algebra_2634
    (a b c : ℚ)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (a - b) / (b - c) > 0 ∧ (b - c) / (c - a) < 0 ∧ (c - a) / (a - b) < 0 ∨
    (a - b) / (b - c) < 0 ∧ (b - c) / (c - a) > 0 ∧ (c - a) / (a - b) < 0 ∨
    (a - b) / (b - c) < 0 ∧ (b - c) / (c - a) < 0 ∧ (c - a) / (a - b) > 0
      := by
      -- Consider the case where \( a > b \).
      by_cases hab : a > b
      · by_cases hac : c > a
        -- Subcase 1: \( c > a > b \).
        · have h1 : c - a > 0 := by linarith
          have h2 : a - b > 0 := by linarith
          have h3 : b - c < 0 := by linarith
          right
          right
          constructor
          -- \((a - b) / (b - c)\) is negative because \(a - b > 0\) and \(b - c < 0\).
          · apply div_neg_of_pos_of_neg h2 h3
          · constructor
            -- \((b - c) / (c - a)\) is negative because \(b - c < 0\) and \(c - a > 0\).
            · apply div_neg_of_neg_of_pos h3 h1
            -- \((c - a) / (a - b)\) is positive because \(c - a > 0\) and \(a - b > 0\).
            · apply div_pos h1 h2
        -- Subcase 2: \( a > b \) and \( a > c \).
        · by_cases hbc : b > c
          · have h1 : a - b > 0 := by linarith
            have h2 : b - c > 0 := by linarith
            have h3 : c - a < 0 := by linarith
            left
            constructor
            -- \((a - b) / (b - c)\) is positive because \(a - b > 0\) and \(b - c > 0\).
            · apply div_pos h1 h2
            · constructor
              -- \((b - c) / (c - a)\) is negative because \(b - c > 0\) and \(c - a < 0\).
              · apply div_neg_of_pos_of_neg h2 h3
              -- \((c - a) / (a - b)\) is negative because \(c - a < 0\) and \(a - b > 0\).
              · apply div_neg_of_neg_of_pos h3 h1
          -- Subcase 3: \( b \leq c \).
          · have h1 : c - a < 0 := by
              simp at hac
              by_contra h
              simp at h
              have : a = c := by linarith
              apply habc.2.1 this
            have h2 : b - c < 0 := by
              simp at hbc
              by_contra h
              simp at h
              have : b = c := by linarith
              apply habc.2.2 this
            have h3 : a - b > 0 := by linarith
            right
            left
            constructor
            -- \((a - b) / (b - c)\) is negative because \(a - b > 0\) and \(b - c < 0\).
            · apply div_neg_of_pos_of_neg h3 h2
            · constructor
              -- \((b - c) / (c - a)\) is positive because \(b - c < 0\) and \(c - a < 0\).
              · apply div_pos_of_neg_of_neg h2 h1
              -- \((c - a) / (a - b)\) is negative because \(c - a < 0\) and \(a - b > 0\).
              · apply div_neg_of_neg_of_pos h1 h3
      -- Consider the case where \( a \leq b \).
      · by_cases hac : a > c
        -- Subcase 4: \( a > c \) and \( b > a \).
        · have h1 : b - c > 0 := by linarith
          have h2 : c - a < 0 := by linarith
          have h3 : a - b < 0 := by
            simp at hab
            by_contra h
            simp at h
            have : a = b := by linarith
            apply habc.1 this
          right
          right
          constructor
          -- \((a - b) / (b - c)\) is negative because \(a - b < 0\) and \(b - c > 0\).
          · apply div_neg_of_neg_of_pos h3 h1
          · constructor
            -- \((b - c) / (c - a)\) is negative because \(b - c > 0\) and \(c - a < 0\).
            · apply div_neg_of_pos_of_neg h1 h2
            -- \((c - a) / (a - b)\) is positive because \(c - a < 0\) and \(a - b < 0\).
            · apply div_pos_of_neg_of_neg h2 h3
        -- Subcase 5: \( a \leq c \) and \( b > c \).
        · by_cases hbc : b > c
          · have h1 : b - c > 0 := by linarith
            have h2 : c - a > 0 := by
              simp at hac
              by_contra h
              simp at h
              have : a = c := by linarith
              apply habc.2.1 this
            have h3 : a - b < 0 := by linarith
            right
            left
            constructor
            -- \((a - b) / (b - c)\) is negative because \(a - b < 0\) and \(b - c > 0\).
            · apply div_neg_of_neg_of_pos h3 h1
            · constructor
              -- \((b - c) / (c - a)\) is positive because \(b - c > 0\) and \(c - a > 0\).
              · apply div_pos h1 h2
              -- \((c - a) / (a - b)\) is negative because \(c - a > 0\) and \(a - b < 0\).
              · apply div_neg_of_pos_of_neg h2 h3
          -- Subcase 6: \( b \leq c \).
          · have h1 : c - a > 0 := by
              simp at hac
              by_contra h
              simp at h
              have : a = c := by linarith
              apply habc.2.1 this
            have h2 : b - c < 0 := by
              simp at hbc
              by_contra h
              simp at h
              have : b = c := by linarith
              apply habc.2.2 this
            have h3 : a - b < 0 := by
              simp at hab
              by_contra h
              simp at h
              have : a = b := by linarith
              apply habc.1 this
            left
            constructor
            -- \((a - b) / (b - c)\) is positive because \(a - b < 0\) and \(b - c < 0\).
            · apply div_pos_of_neg_of_neg h3 h2
            · constructor
              -- \((b - c) / (c - a)\) is negative because \(b - c < 0\) and \(c - a > 0\).
              · apply div_neg_of_neg_of_pos h2 h1
              -- \((c - a) / (a - b)\) is negative because \(c - a > 0\) and \(a - b < 0\).
              · apply div_neg_of_pos_of_neg h1 h3
