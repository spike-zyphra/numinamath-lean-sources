import Mathlib

theorem number_theory_205670 :
    ∃ f : Fin 6 → ℕ,
      (∀ i j, i ≠ j → f i + f j < 40 / 2) ∧
      (∀ i, f i > 0) ∧
      (∀ i, ∀ j, f i = f j → i = j) := by

  use λ i => match i with
    | 0 => 4
    | 1 => 5
    | 2 => 6
    | 3 => 7
    | 4 => 8
    | 5 => 10
    | _ => 0

  constructor
  · -- Show that for any i ≠ j, f i + f j < 20
    intros i j h_ineq
    fin_cases i <;> fin_cases j <;> simp at h_ineq ⊢ <;> omega
  constructor
  · -- Show that each f i > 0
    intro i
    fin_cases i <;> simp
  · -- Show that f is injective
    intro i j h_eq
    fin_cases i <;> fin_cases j <;> simp [h_eq] at *
    <;> omega