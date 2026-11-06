import Mathlib

/- Problem 8.8.1. Different positive numbers $a, b, c$ are such that


$$

\left\{\begin{array}{l}
a^{2}+b c=115 \\
b^{2}+a c=127 \\
c^{2}+a b=115
\end{array}\right.

$$


Find $a+b+c$. -/
theorem algebra_101522 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≠ b) (h2 : b ≠ c) (h3 : c ≠ a) (h4 : a^2 + b * c = 115) (h5 : b^2 + a * c = 127)
    (h6 : c^2 + a * b = 115) : a + b + c = 22 := by

      --Subtracting `h6` from `h4` and transforming yields...
      have h₁ : (a - c) * (a + c - b) = 0 := by
        linarith

      --`h3` yields (a - c) ≠ 0
      have h₂ : a - c ≠ 0 := by
        exact sub_ne_zero_of_ne (id (Ne.symm h3))

      --Cancel out a - c from `h₁` and obtain a + c = b
      have h₃ : a + c = b := by
        have : a + c - b = 0 := by
          exact (mul_eq_zero_iff_left h₂).mp h₁
        linarith

      --Adding the first two equations yields...
      have h₄ : (a^2 + b * c) + (b^2 + a * c) = 242 := by
        linarith

      --Substituting a + c = b yields...
      have h₅ : 2 * (a + c)^2 = 242 := by
        calc
          _ = a^2 + a * c + c^2 + (a + c)^2 + a * c := by ring
          _ = a^2 + (a + c) * c + (a + c)^2 + a * c := by ring
          _ = a^2 + b * c + b^2 + a * c := by rw [h₃]
          _ = (a^2 + b * c) + (b^2 + a * c) := by ring
          _ = 242 := by rw [h₄]

      --Dividing the equaiton `h₅` by 2 yields...
      have h₆ : (a + c)^2 = 121 := by
        have h₆_1 : 2 * ((a + c)^2 - 121) = 0 := by linarith
        have h₆_2 : (a + c)^2 - 121 = 0 := by linarith
        linarith

      --Taking squareroot yields...
      have h₇ : a + c = 11 ∨ a + c = -11 := by
        refine sq_eq_sq_iff_eq_or_eq_neg.mp ?_
        have : 11^2 = 121 := by norm_num
        linarith

      --Show a + c = -11 is impossible by way of contradiction.
      have h₈ : ¬ (a + c = -11) := by
        by_contra h₈
        have : a + c > 0 := by positivity
        have : -11 > 0 := by linarith
        contradiction

      --Obtain a + c = 11.
      have h₉ : a + c = 11 := by
        tauto

      --Obtain b = 11 using `h3`
      have h₁0 : b = 11 := by
        linarith

      --Now `linarith` closes the goal.
      linarith