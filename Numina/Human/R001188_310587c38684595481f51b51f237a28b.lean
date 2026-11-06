import Mathlib

/- Let $a,$ $b,$ and $c$ be real numbers such that $a + b + c = 0$ and $a^2 + b^2 + c^2 = 4.$  Find $a^4 + b^4 + c^4.$ -/
theorem algebra_20968 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a^2 + b^2 + c^2 = 4) :
    a^4 + b^4 + c^4 = 8 := by
  -- $ab + ac + bc = -2$
  have abeq : a * b + a * c + b * c = -2 := by
    -- $ab + ac + bc = ((a + b + c)^2 - (a^2 + b^2 + c^2)) / 2$
    have eq : a * b + a * c + b * c = ((a + b + c) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2)) / 2 := by
      ring
    norm_num [eq, h₀, h₁]
  -- $a^2b^2 + a^2c^2 + b^2c^2 = 4$
  have absqeq : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 = 4 := by
    -- $a^2b^2 + a^2c^2 + b^2c^2 = ((a^2 + b^2 + c^2)^2 - 2(a^2b^2 + a^2c^2 + b^2c^2))$
    have eq : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 = (a * b + a * c + b * c) ^ 2 - 2 * a * b * c * (a + b + c) := by
      ring
    norm_num [eq, abeq, h₀]
  -- $a^4 + b^4 + c^4 = (a^2 + b^2 + c^2) ^ 2 - 2(a^2b^2 + a^2c^2 + b^2c^2)$
  have eq : a^4 + b^4 + c^4 = (a^2 + b^2 + c^2) ^ 2 - 2 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) := by
    ring
  -- $a^4 + b^4 + c^4 = 8$
  norm_num [eq, absqeq, h₁]