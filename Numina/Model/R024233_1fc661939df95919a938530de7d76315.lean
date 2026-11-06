import Mathlib

theorem inequalities_195670 (a b c x y z : ℕ) (h₀ : a^2 + b^2 = c^2) (h₁ : x^2 + y^2 = z^2) :
    (a + x)^2 + (b + y)^2 ≤ (c + z)^2 := by
  ring_nf at *
  nlinarith [sq_nonneg ((a : ℕ) * (y : ℕ) - (b : ℕ) * (x : ℕ) : ℤ),
          sq_nonneg ((a : ℕ) * (z : ℕ) - (c : ℕ) * (x : ℕ) : ℤ),
          sq_nonneg ((b : ℕ) * (z : ℕ) - (c : ℕ) * (y : ℕ) : ℤ),
          sq_nonneg ((c : ℕ) * (z : ℕ) - (a : ℕ) * (x : ℕ) - (b : ℕ) * (y : ℕ) : ℤ),
          mul_nonneg (show (0 : ℕ) ≤ a by nlinarith) (show (0 : ℕ) ≤ b by nlinarith),
          mul_nonneg (show (0 : ℕ) ≤ a by nlinarith) (show (0 : ℕ) ≤ x by nlinarith),
          mul_nonneg (show (0 : ℕ) ≤ a by nlinarith) (show (0 : ℕ) ≤ y by nlinarith),
          mul_nonneg (show (0 : ℕ) ≤ b by nlinarith) (show (0 : ℕ) ≤ x by nlinarith),
          mul_nonneg (show (0 : ℕ) ≤ b by nlinarith) (show (0 : ℕ) ≤ y by nlinarith),
          mul_nonneg (show (0 : ℕ) ≤ x by nlinarith) (show (0 : ℕ) ≤ y by nlinarith),
          mul_nonneg (show (0 : ℕ) ≤ c by nlinarith) (show (0 : ℕ) ≤ z by nlinarith)]