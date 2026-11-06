import Mathlib

theorem number_theory_185353 :
    ∃ b : Fin 10 → ℕ,
      (∀ i, 7 ∈ Nat.digits 10 (b i)) ∧
      (∑ i, b i) = 2017 := by
  use λ i =>
    match i.val with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => 107
    | 8 => 370
    | 9 => 791
    | _ => 0 -- This case is impossible as Fin 10 only goes up to 9
  constructor
  · -- Show that each b i contains the digit 7
    intro i
    fin_cases i <;> simp
    all_goals
      native_decide
  · -- Show that the sum of b i is 2017
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> try { native_decide }