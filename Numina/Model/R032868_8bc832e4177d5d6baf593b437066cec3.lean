import Mathlib

def fib (n : ℕ) : ℕ := match n with
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

theorem algebra_164543 {n : ℕ} :
    ∑ k in Finset.Icc 1 n, (fib k)^2 = fib n * fib (n + 1) := by
  have h1 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, (fib k)^2 = fib n * fib (n + 1) := by 
    intro n 
    induction n with 
    | zero => 
      simp [fib]
    | succ n ihn =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp [fib] at ihn ⊢ 
      all_goals try { 
        ring_nf at ihn ⊢ 
        omega 
      }
      all_goals try { 
        nlinarith [ihn]
      }
      all_goals try { 
        induction n with 
        | zero => 
          simp [fib] 
        | succ n ih => 
          simp [fib] at ih ⊢ 
          all_goals try { 
            nlinarith [ih]
          } 
      }
  apply h1 n