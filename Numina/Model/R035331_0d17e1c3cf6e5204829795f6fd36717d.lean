import Mathlib

theorem algebra_246806 (f : ℕ → ℤ) (hf : ∀ n, f n = ∑ i in Finset.Icc 1 n, i) :
    ∀ n, f n = n * (n + 1) / 2 := by 
  intro n 
  have h1 : ∀ n, f n = n * (n + 1) / 2 := by 
    intro n
    induction n with
    | zero =>
      have h2 : f 0 = ∑ i in Finset.Icc 1 0, i := hf 0 
      simp [Finset.sum_eq_zero] at h2 ⊢ 
      linarith [h2]
    | succ n ih =>
      have eq1 : f (n + 1) = f n + (↑n + 1 : ℤ) := by 
        rw [hf (n + 1), hf n]
        simp [Finset.sum_Icc_succ_top] 
      have eq2 : f (n + 1) = (↑n + 1 : ℤ) + f n := by 
        linarith [eq1]
      rw [eq2]
      rw [ih]
      simp [Int.add_emod, Int.mul_emod, add_assoc] 
      all_goals try { 
        ring_nf <;> omega 
      }
  exact h1 n