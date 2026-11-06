import Mathlib

theorem number_theory_157556 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (100 * a + 10 * b + c) + (100 * a + 10 * c + b) +
    (100 * b + 10 * a + c) + (100 * b + 10 * c + a) +
    (100 * c + 10 * a + b) + (100 * c + 10 * b + a) ≠ 2021 := by 
  have h1 : (100 * a + 10 * b + c) + (100 * a + 10 * c + b) +
      (100 * b + 10 * a + c) + (100 * b + 10 * c + a) +
      (100 * c + 10 * a + b) + (100 * c + 10 * b + a) = 222 * (a + b + c) := by
    ring
  rw [h1]
  -- Let's prove equality to 2021 is impossible
  omega