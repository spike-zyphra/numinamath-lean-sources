import Mathlib

theorem algebra_7027 (n : ℕ) (a : ℕ → ℤ) (h₀ : a 0 = -2468) (h₁ : a (n - 1) = 2464)
    (h₂ : ∀ i, a (i + 1) = a i + 4) :
    ∑ i in Finset.range n, a i = -2468 := by
  have h3 : ∀ i : ℕ, a i = -2468 + 4 * (i : ℤ) := by
    intro i
    induction i with 
    | zero =>
      simp [h₀]
    | succ i ih =>
      have h4 : a (i + 1) = a i + 4 := h₂ i
      rw [h4]
      rw [ih]
      simp [add_mul, mul_add, add_assoc]
      <;> ring
  have h5 : n = 1234 := by 
    have h8 : a (n - 1) = -2468 + 4 * ((n - 1 : ℕ) : ℤ) := h3 (n - 1)
    rw [h8] at h₁
    have : (n : ℤ) = 1234 := by
      cases n with
      | zero => 
        exfalso
        omega
      | succ n => 
        simp at h₁ ⊢
        omega
    omega
  rw [h5]
  -- Work with Lean  to compute a large explicit summation result
  norm_num [Finset.sum_range_succ, h3]
  <;> native_decide