import Mathlib

theorem algebra_173934 (a b c d p q r s : ℝ) :
    (a * p + b * q + c * r + d * s)^2 +
    (a * q - b * p + c * s - d * r)^2 +
    (a * r - b * s - c * p + d * q)^2 +
    (a * s + b * r - c * q - d * p)^2 =
    (a^2 + b^2 + c^2 + d^2) * (p^2 + q^2 + r^2 + s^2) := by 
  ring