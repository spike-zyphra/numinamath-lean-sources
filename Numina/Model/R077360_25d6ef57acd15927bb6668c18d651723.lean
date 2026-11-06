import Mathlib

open Finset

theorem number_theory_7279 {F : ℕ → ℤ} (hF : ∀ n, F (n + 1) = F n + F (n - 1)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∀ n ≥ 1, F (n + 1)^2 - F n * F (n + 2) = (-1)^n := by 
  intro n hn 
  induction n with 
  | zero => 
    exfalso 
    exact Nat.lt_irrefl 0 hn 
  | succ n ih =>
    cases n with 
    | zero =>
      simp [pow_two, hF, hF0, hF1] at *
      <;> norm_num [pow_two, hF, hF0, hF1] at *
    | succ n =>
      simp [pow_two, hF, hF0, hF1, mul_add, add_mul, pow_two] at ih ⊢ 
      <;> ring_nf at ih ⊢ 
      <;> nlinarith [ih]