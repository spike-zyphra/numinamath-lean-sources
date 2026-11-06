import Mathlib

theorem algebra_299592 {x y a : ℝ} (h₀ : x + y = a) (h₁ : x ^ 3 + y ^ 3 = a) (h₂ : x ^ 5 + y ^ 5 = a) :
    a = 2 ∨ a = -2 ∨ a = 1 ∨ a = -1 ∨ a = 0 := by
  have eq1 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
    ring
  rw [show x + y = a by linarith [h₀]] at eq1
  have h₃ : a ^ 3 - 3 * (x * y) * a = a := by linarith [show x ^ 3 + y ^ 3 = a by linarith [h₁], eq1]
  have h₄ : a * (a ^ 2 - 1 - 3 * (x * y)) = 0 := by
    nlinarith
    <;> nlinarith [h₀]

  cases (mul_eq_zero.mp h₄) with
  | inl h₅ =>
    -- Case where $a = 0$ so we need to prove $a = 0$
    right
    right
    right
    right
    linarith
  | inr h₅ =>
    -- Case where $a^2 - 1 - 3 * (x * y) = 0$ so $3 * (x * y) = a^2 - 1$
    have h₆ : x * y = (a ^ 2 - 1) / 3 := by
      nlinarith
    -- Let's express $x^5 + y^5$ using the identity
    -- $x^5 + y^5 = (x + y)^5 - 5xy(x + y)^3 + 5(xy)^2(x + y)$
    have eq2 : x ^ 5 + y ^ 5 = (x + y) ^ 5 - 5 * (x * y) * (x + y) ^ 3 + 5 * (x * y) ^ 2 * (x + y) := by
      ring_nf
      <;> nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y - a)]

    rw [show x + y = a by linarith [h₀], h₆] at eq2
    -- Now substitute $a$ for $x + y$ and solve $x^5 + y^5 = a$.
    -- The result is a polynomial in $a$ that will yield all possible values of $a$.

    have h₇ : (a - 2) * (a + 2) * (a - 1) * (a + 1) * a = 0 := by
      nlinarith
      <;> nlinarith [sq_nonneg ((a ^ 2)), sq_nonneg ((a ^ 2 - 1)), sq_nonneg ((a ^ 2 - 4)), sq_nonneg (x - y), sq_nonneg (x * y - (a^2 - 1)/3)]

    cases (mul_eq_zero.mp h₇) with
    | inl h₈ =>
      cases (mul_eq_zero.mp h₈) with
      | inl h₉ =>
        cases (mul_eq_zero.mp h₉) with
        | inl h10 =>
          cases (mul_eq_zero.mp h10) with
          | inl h11 =>
            left
            linarith
          | inr h11 =>
            right
            left
            nlinarith
        | inr h10 =>
          right
          right
          left
          nlinarith
      | inr h9 =>
        right
        right
        right
        left
        nlinarith
    | inr h8 =>
      right
      right
      right
      right
      nlinarith