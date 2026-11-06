import Mathlib

open Finset

theorem number_theory_129643 {f : ℕ → ℕ} (hf1 : f 1 = 2)
    (hfn : ∀ n, f (n + 1) = 2 * f n) :
    ∃ m, ∀ n, f n % m = f (n + 1) % m := by 
  have h1 : ∀ (n : ℕ), f (n + 1) = 2 * f n := by
    intro n
    specialize hfn n
    simpa using hfn 
  have f1 : f 1 = 2 := hf1 
  have f0 : f 0 = 1 := by
    have eq1 := h1 0 
    simp at eq1 
    omega 
  use 1 
  intro n
  have h1' : ∀ (n : ℕ), f n % 1 = 0 := by 
    intro n 
    induction n with 
    | zero => 
      simp [f0]
    | succ n ih =>
      have eq1 : f (n + 1) = 2 * f n := h1 n
      simp [eq1] at *
      all_goals omega
  have h1n : f n % 1 = 0 := h1' n 
  have h1n1 : f (n + 1) % 1 = 0 := h1' (n + 1) 
  simp [h1n, h1n1]