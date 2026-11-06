import Mathlib

def p (n : ℕ) := (Nat.digits 10 n).prod
def s (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_95147 {N : ℕ} (hN : N ∈ Finset.Icc 10 99) (h : N = p N + s N) :
    N % 10 = 9 := by
  rw [Finset.mem_Icc] at hN
  rcases hN with ⟨h10, h99⟩
  interval_cases N <;> norm_num [p, s] at h ⊢ <;> omega