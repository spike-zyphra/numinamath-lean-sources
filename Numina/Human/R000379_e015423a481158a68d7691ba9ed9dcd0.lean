import Mathlib

/- Think about it, can you find the integer $a=$ ____ when the solution to the equation $ax=3$ is a natural number.-/
theorem algebra_9304 {a : ℤ} (ha : ∃ x : ℕ, a * x = 3) :
    a = 1 ∨ a = 3 := by
  -- It's clear that divisors of 3 are 1 and 3.
  have divisors3 : Nat.divisors 3 = {1, 3} := by native_decide
  rcases ha with ⟨x, hx⟩
  -- It's clear that x is a divisor of 3.
  have : x ∣ 3 := by zify; use a; linear_combination -hx
  have : x ∈ Nat.divisors 3 := by rw [Nat.mem_divisors]; exact ⟨this, by norm_num⟩
  rw [divisors3] at this
  simp at this
  rcases this with hx1 | hx3
  -- Hence x = 1
  . rw [hx1] at hx
    norm_num at hx
    right
    -- We can deduce a=3 from x=1.
    exact hx
  -- or x = 3
  rw [hx3] at hx
  norm_num at hx
  left
  -- We can deduce a=1 from x=1.
  exact hx
