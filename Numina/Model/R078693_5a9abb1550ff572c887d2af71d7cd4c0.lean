import Mathlib

theorem algebra_297575 {f : ℕ → ℕ} (h : ∀ m n, f (m + n) = f m + f n + m * n)
    (h' : f 1 = 1) :
    ∀ n, f n = (n * (n + 1)) / 2 := by
  have f0 : f 0 = 0 := by
    specialize h 0 0 
    simp at h ⊢ 
    omega 
  have eq1 : ∀ k, f (k + 1) = f k + k + 1 := by 
    intro k 
    have eq2 := h 1 k 
    simp [h', add_comm, add_assoc] at eq2 ⊢ 
    <;> ring_nf at eq2 ⊢ 
    <;> omega 
  intro n 
  induction' n using Nat.strongRecOn with n ih 
  cases n with 
  | zero => 
    simp [f0]
  | succ n => 
    have eq2 : f (n + 1) = f n + (n : ℕ) + 1 := eq1 n 
    have h_n : f n = (n * (n + 1)) / 2 := ih (n) (by linarith) 
    rw [eq2, h_n]
    cases n with 
    | zero => 
      simp [h']
      <;> ring_nf <;> omega 
    | succ n => 
      simp [Nat.mul_add, Nat.add_mul, mul_add, add_mul, Nat.mul_assoc, Nat.add_assoc]
      <;> ring_nf 
      <;> omega 
      <;> ring_nf <;> omega