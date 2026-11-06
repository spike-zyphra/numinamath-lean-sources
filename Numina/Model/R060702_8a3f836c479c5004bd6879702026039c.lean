import Mathlib

theorem algebra_117228 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 1) = a n + 2) (h₁ : ∑ i in Finset.range 8, a i = ∑ i in Finset.range 4, a (11 - i)) :
    a 1 = 7 := by
  have h2 : ∀ n : ℕ, a n = a 0 + 2 * (n : ℕ) := by
    intro n
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      have eq1 : a (n + 1) = a n + 2 := h₀ n 
      rw [eq1, ih]
      simp [Nat.mul_add, Nat.add_mul]
      <;> ring 
  have eq1 : ∑ i in Finset.range 8, a i = 8 * a 0 + 56 := by 
    simp [Finset.sum_range_succ, h2 1, h2 2, h2 3, h2 4, h2 5, h2 6, h2 7]
    ring_nf 
  have eq2 : ∑ i in Finset.range 4, a (11 - i) = 4 * a 0 + 76 := by 
    simp [Finset.sum_range_succ, h2 11, h2 10, h2 9, h2 8]
    ring_nf 
    <;> linarith 
  rw [eq1] at h₁ 
  rw [eq2] at h₁ 
  have ha0 : a 0 = 5 := by
    linarith 
  have ha1 : a 1 = a 0 + 2 := h₀ 0 
  rw [ha0] at ha1 
  linarith