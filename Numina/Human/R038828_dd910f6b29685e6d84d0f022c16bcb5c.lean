import Mathlib

/- Show that if $a$ and $b$ are integer numbers, and $a^2 + b^2 + 9ab$ is divisible by $11$, then $a^2-b^2$ divisible by $11$. -/
theorem number_theory_87205 (a b : ℤ) (h : 11 ∣ a^2 + b^2 + 9 * a * b) : 11 ∣ a^2 - b^2 := by
  -- To prove divisibility by 11, verify divisibility of $a^2 + b^2 + 9ab$ by 11
  rw [Int.dvd_iff_emod_eq_zero] at h ⊢
  have h1 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by 
    omega
  have h2 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by 
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;>
  rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;>
  simp [h1, h2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h ⊢