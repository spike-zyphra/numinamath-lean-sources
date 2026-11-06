import Mathlib

/- In multiplying two positive integers aa and bb, Ron reversed the digits of
\  the two-digit number a. His erroneous product was 161. What is the correct
\  value of the product of a and b?
(A) 116 (B) 161 (C) 204 (D) 214 (E) 224 -/
theorem number_theory_94948 (a b : ℕ)
(ha : 10 ≤ a ∧ a < 100)
(h : a * b = 161) :
(10 * (a % 10) + (a / 10)) * b = 224 := by {
  suffices : a = 23 -- Begin by showing that the claim follows if a = 23. This is because it implies b = 7, and then one can just plug in the values to obtain the claim.
  rw [this] at h
  have h2 : b = 7 := by linarith [this, h]
  rw [this, h2]
  -- We now show that a = 23. First, we note that we have a ∈ {1,7,23,161}, and the reason is that a is a divisor of 161.
  set dv := ({1, 7, 23, 161} : Finset ℕ)
  have h1: a ∈ Nat.divisors 161 := by {simp; rw [← h]; simp}
  have h2: a ∈ dv := by exact h1
  aesop
}