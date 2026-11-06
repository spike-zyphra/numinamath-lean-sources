import Mathlib

theorem algebra_19797 (x : ℕ) : (3 : ℤ)^(x + 8) = (9 : ℤ)^(x + 3) ↔ x = 2 := by
  constructor
  · -- Forward direction: Assume (3 : ℤ)^(x + 8) = (9 : ℤ)^(x + 3) prove x = 2
    intro h
    have h1 : (9 : ℤ) ^ (x + 3) = (3 : ℤ) ^ (2 * (x + 3 : ℕ)) := by
      rw [show (9 : ℤ) = 3 ^ (2 : ℕ) by norm_num]
      rw [pow_mul]
      <;> norm_num
    rw [h1] at h
    have h2 : (x + 8 : ℕ) = (2 * (x + 3 : ℕ)) := by
      have h3 : (3 : ℤ) ^ (x + 8) = (3 : ℤ) ^ (2 * (x + 3 : ℕ)) := h
      have h4 : (x + 8 : ℕ) = (2 * (x + 3 : ℕ) : ℕ) := by
        exact Nat.cast_injective (by simpa using h3)
      linarith
    -- Solve equation
    have h3 : (x : ℕ) = 2 := by
      omega
    exact h3
  · -- Reverse direction: Assume x = 2 prove (3 : ℤ)^(x + 8) = (9 : ℤ)^(x + 3)
    intro h
    rw [h]
    norm_num
    <;> try { ring }