import Mathlib

/- PROBLEM: At each basketball practice last week, Jenny made twice as many free throws as she made at the previous practice. At her fifth practice she made 48 free throws. How many free throws did she make at the first practice? -/
theorem algebra_96805 
  (a b c d e : ℕ) 
  (h₀ : 2 * a = b) 
  (h₁ : 2 * b = c) 
  (h₂ : 2 * c = d) 
  (h₃ : 2 * d = e) 
  (h₄ : e = 48) : 
  a = 3 := 
by {
  rw [←h₃, ←h₂, ←h₁, ←h₀, ←mul_assoc, ←mul_assoc, ←mul_assoc] at h₄
  simp at h₄
  have : 0 < 16 := by trivial
  apply Nat.mul_left_cancel this
  exact h₄
}