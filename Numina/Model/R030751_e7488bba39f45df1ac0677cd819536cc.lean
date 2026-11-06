import Mathlib

theorem algebra_109876 {n : ℕ} (hn : n > 0) :
    ∑ k in Finset.Icc 1 n, k^2 = n * (n + 1) * (2 * n + 1) / 6 := by 
  induction n with 
  | zero => 
    linarith 
  | succ n ih => 
    cases n with
    | zero => 
      simp 
    | succ n => 
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih (by linarith)]
      ring_nf
      omega