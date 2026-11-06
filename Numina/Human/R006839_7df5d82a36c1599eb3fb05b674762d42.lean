import Mathlib

open Finset Nat

def a : ℕ → ℕ
| 0 => 1
| 1 => 2
| n + 2 => a n + a (n + 1)


theorem number_theory_641627 {M : ℕ} (hM : M > 0) :
  ∑ i ∈ range M, a i = fib M + 2 * (fib (M + 1) - 1) := by 
  have h1 : ∀ n, a n = fib (n + 2) ∧ a (n + 1) = fib (n + 3) := by 
    intro n
    induction n with
    | zero => 
      simp
      unfold a
      simp
      exact rfl
    | succ k ih => 
      obtain ⟨ih1, ih2⟩ := ih
      constructor 
      · exact ih2
      · unfold a
        rw [ih1, ih2]
        exact Eq.symm fib_add_two
  induction' hM with k ih1 ih2
  · simp
    unfold a
    rfl
  · simp at ih1 
    have aux1 : range k.succ = insert k (range k) := by
      exact range_add_one
    rw [aux1, sum_insert, ih2]
    simp
    rw [(h1 k).1, fib_add_two]
    zify
    have cast1 : (fib (k + 1) - 1 : ℕ) = (fib (k + 1) - (1 : ℤ)) := by 
      have ge1 : fib (k + 1) ≥  1 := by 
        obtain aux := le_fib_add_one (k + 1)
        linarith
      omega
    have cast2 : ↑(fib k + fib (k + 1) - 1 : ℕ) = (fib k + fib (k + 1) - (1 : ℤ)) := by 
      have ge1 : fib k + fib (k + 1) ≥ 1 := by 
        rw [←fib_add_two]
        obtain aux := le_fib_add_one (k + 2)
        linarith
      omega
    rw [cast1, cast2]
    ring_nf
    simp