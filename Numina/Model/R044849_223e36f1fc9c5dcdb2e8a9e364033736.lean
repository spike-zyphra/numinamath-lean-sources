import Mathlib

/- Originally given matrix `U=[1,1; 0,1]` which is wrong.
It should be `U=[1,1; 1,0]`. -/
abbrev U : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/- Fibonacci number -/
abbrev fib : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem number_theory_4548_1 {n : ℕ} (h_posn : n ≥ 0) :
    U ^ (n + 1) = !![fib (n + 2), fib (n + 1); fib (n + 1), fib (n)] := by
  -- use mathematical induction
  induction n with
  -- check base case
  | zero => norm_num
  | succ n ih =>
    -- use the fact that `U^(n+1)=U^n*U`
    -- we can draw a conclusion from induction hypothesis after simple calculation
    rw [pow_succ, ih (Nat.zero_le n), U]
    norm_num
    ring_nf

theorem number_theory_4548_2
    (n : ℕ) (h_posn : n > 0)
    (h : ∀ n, fib (n + 1) * fib (n - 1) - (fib n) ^ 2 = (-1) ^ n) :
    (U ^ n).det = (-1) ^ n := by
  have eq1 : (U ^ n) = !![fib (n + 1), fib n; fib n, fib (n - 1 : ℕ)] := by
    have h2 : ∀ (k : ℕ), U ^ (k + 1) = !![fib (k + 2), fib (k + 1); fib (k + 1), fib k] := by
      intro k 
      induction k with 
      -- check base case
      | zero => norm_num 
      | succ k ih => 
        -- use the fact that `U^(k+1)=U^k*U`
        -- we can draw a conclusion from induction hypothesis after simple calculation
        rw [pow_succ, ih, U]
        norm_num
        ring_nf 
    have h3 : n - 1 + 1 = n := by omega
    have eq1_n1 : U ^ ( (n - 1) + 1 ) = !![fib ( (n - 1) + 2 ), fib ( (n - 1) + 1 ); fib ( (n - 1) + 1 ), fib (n - 1)] := h2 (n - 1)
    rw [show (n - 1) + 1 = n by omega] at eq1_n1
    simpa [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega] using eq1_n1

  rw [eq1]
  simp [Matrix.det_fin_two, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h4 : (n : ℕ) > 0 := h_posn 
  have h5 := h n
  have h6 : fib (n + 1) * fib (n - 1) - (fib n) ^ 2 = (-1) ^ n := h5 
  have eq7 : (fib n) ^ 2 = fib n * fib n := by 
    ring 
  have h8 : fib (n + 1) * fib (n - 1) - fib n * fib n = (-1) ^ n := by 
    have h9 : (fib (n + 1) * fib (n - 1) - (fib n) ^ 2) = (fib (n + 1) * fib (n - 1) - fib n * fib n) := by 
      rw [eq7] 
    rw [h9] at h6 
    linarith 
  simpa using h8