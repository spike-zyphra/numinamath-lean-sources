import Mathlib

/- The real numbers $a, b, c$ are such that $a^{2}+b^{2}=2 c^{2}$, and also such that $a \neq b, c \neq-a, c \neq-b$. Show that

$$
\frac{(a+b+2 c)\left(2 a^{2}-b^{2}-c^{2}\right)}{(a-b)(a+c)(b+c)}
$$

is an integer. -/
theorem algebra_608014 {a b c : ℝ} (h₀ : a^2 + b^2 = 2 * c^2) (h₁ : a ≠ b)
    (h₂ : c ≠ -a) (h₃ : c ≠ -b) :
    ∃ k : ℤ, ((a + b + 2 * c) * (2 * a^2 - b^2 - c^2)) / ((a - b) * (a + c) * (b + c)) = k := by
  -- rewrite $a + b + 2c$ into $(a + c) + (b + c)$
  rw [show a + b + 2 * c = (a + c) + (b + c) by ring, add_mul]
  -- rewrite one $2a^2 - b^2 - c^2$ into $3(b + c)(c - b)$
  have : 2 * a ^ 2 - b ^ 2 - c ^ 2 = 3 * (b + c) * (c - b) := by linear_combination 2 * h₀
  nth_rw 1 [this]
  -- rewrite the other $2a^2 - b^2 - c^2$ into $3(a + c)(a - c)$
  have : 2 * a ^ 2 - b ^ 2 - c ^ 2 = 3 * (a + c) * (a - c) := by linear_combination -h₀
  -- use distributivity
  rw [
    this,
    show (a + c) * (3 * (b + c) * (c - b)) = 3 * (a + c) * (b + c) * (c - b) by ring,
    show (b + c) * (3 * (a + c) * (a - c)) = 3 * (a + c) * (b + c) * (a - c) by ring,
    <-mul_add,
    show c - b + (a - c) = a - b by ring,
    show 3 * (a + c) * (b + c) * (a - b) = 3 * ((a - b) * (a + c) * (b + c)) by ring,
    mul_div_cancel_right₀,
  ]
  -- so the expression is equal to 3
  use 3
  simp
  -- prove the denominator is not zero
  simp
  constructor
  constructor
  rw [sub_eq_zero]
  exact h₁
  rw [add_comm, add_eq_zero_iff_eq_neg]
  exact h₂
  rw [add_comm, add_eq_zero_iff_eq_neg]
  exact h₃
