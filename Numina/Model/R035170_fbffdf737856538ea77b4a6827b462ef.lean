import Mathlib

open Finset Real

theorem other_48012 {x : ℕ → ℝ}
    (hx1 : x 1 = 0) (hx2 : x 2 = 1 / 2)
    (hxn : ∀ n > 2, x n = (x (n - 1) + x (n - 2)) / 2) :
    ∀ n ≥ 1, x (n + 1) - x n = (-1) ^ (n - 1) / 2 ^ n := by 
  intro n hn 
  induction n with
  | zero => 
    exfalso 
    omega 
  | succ n ih => 
    cases n with 
    | zero => 
      rw [hx1, hx2]
      norm_num 
    | succ n => 
      have eq2 : x (n + 3) = (x (n + 2) + x (n + 1)) / 2 := by 
        specialize hxn (n + 3) (by linarith)
        simpa using hxn 
      have eq3 : x (n + 2) - x (n + 1) = (-1) ^ ((n + 1) - 1) / 2 ^ (n + 1) := by 
        specialize ih (by omega) 
        simpa using ih 
      have eq4 : x (n + 3) - x (n + 2) = - (x (n + 2) - x (n + 1)) / 2 := by 
        rw [eq2] 
        field_simp 
        <;> ring 
      rw [eq4] 
      rw [eq3] 
      field_simp 
      <;> ring_nf