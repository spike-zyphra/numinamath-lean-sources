import Mathlib

theorem number_theory_160836 : (3^3=27 ∧ ∃ x : Fin 3 → ℕ, x 0 + x 1 + x 2 = 21 ∧ 0 < x 0 ∧ x 0 < x 1 ∧ x 1 < x 2) ∧
    (3^5=243 ∧ ∃ x : Fin 3 → ℕ, x 0 + x 1 + x 2 = 57 ∧ 0 < x 0 ∧ x 0 < x 1 ∧ x 1 < x 2) ∧
    (3^7=2187 ∧ ∃ x : Fin 3 → ℕ, x 0 + x 1 + x 2 = 165 ∧ 0 < x 0 ∧ x 0 < x 1 ∧ x 1 < x 2):= by 
  constructor
  · -- Show that 3^3=27 and there exists a function x : Fin 3 → ℕ such that x 0 + x 1 + x 2 = 21 and 0 < x 0 < x 1 < x 2
    constructor
    · -- Show that 3^3=27
      norm_num 
    · -- Show the existence of the function for n = 21
      use λ i =>
        match i with
        | 0 => 3
        | 1 => 7
        | 2 => 11
        | _ => 0
      all_goals simp 
  constructor
  · -- Show that 3^5=243 and there exists a function x : Fin 3 → ℕ such that x 0 + x 1 + x 2 = 57 and 0 < x 0 < x 1 < x 2 
    constructor
    · -- Show that 3^5=243 
      norm_num 
    · -- Show the existence of the function for n = 57
      use λ i =>
        match i with
        | 0 => 10
        | 1 => 18
        | 2 => 29
        | _ => 0 
      all_goals simp 
  · -- Show that 3^7=2187 and there exists a function x : Fin 3 → ℕ such that x 0 + x 1 + x 2 = 165 and 0 < x 0 < x 1 < x 2 
    constructor
    · -- Show that 3^7=2187 
      norm_num 
    · -- Show the existence of the function for n = 165
      use λ i =>
        match i with
        | 0 => 33
        | 1 => 55
        | 2 => 77
        | _ => 0 
      all_goals simp