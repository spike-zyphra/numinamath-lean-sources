import Mathlib

/- Show that an integer $= 7 \mod 8$ cannot be sum of three squares. -/
theorem number_theory_81392 (n : ℤ) (h : n ≡ 7 [ZMOD 8]) :
    ¬∃ a b c, n = a^2 + b^2 + c^2 := by 
  -- Assume a contradictory that n can be obtained: there exist a, b, and c such that n = a^2 + b^2 + c^2}
  rw [Int.ModEq] at h
  rintro ⟨a, b, c, hn⟩
  -- Cross out identical sums: compute all elements mod 8
  have : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by 
    omega
  have : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
    omega
  have : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    omega
  -- Consider modulus edge cases: simplify equation on similar constraints.
  rcases this with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;>
  rcases this with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;>
  rcases this with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;>
  simp [h1, h2, h3, pow_two, Int.ModEq, Int.add_emod, Int.mul_emod, hn] at h
  -- Conclude indirectly – no consequence of shows otherwise.
  <;> omega