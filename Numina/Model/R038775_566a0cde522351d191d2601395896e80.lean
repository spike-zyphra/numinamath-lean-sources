import Mathlib

theorem algebra_170082 (a : Fin 3 → Fin 3 → ℝ)
    (h₀ : ∀ i, ∃ m : ℤ, a i 0 + a i 1 + a i 2 = m)
    (h₁ : ∀ j, ∃ m : ℤ, a 0 j + a 1 j + a 2 j = m) :
    ∃ b : Fin 3 → Fin 3 → ℤ,
      (∀ i, b i 0 + b i 1 + b i 2 = a i 0 + a i 1 + a i 2) ∧
      (∀ j, b 0 j + b 1 j + b 2 j = a 0 j + a 1 j + a 2 j) := by

  -- Extract the row sums
  have h2 := h₀ 0
  rcases h2 with ⟨m0, hm0⟩
  have h3 := h₀ 1
  rcases h3 with ⟨m1, hm1⟩
  have h4 := h₀ 2
  rcases h4 with ⟨m2, hm2⟩

  -- Extract the column sums
  have h5 := h₁ 0
  rcases h5 with ⟨n0, hn0⟩
  have h6 := h₁ 1
  rcases h6 with ⟨n1, hn1⟩
  have h7 := h₁ 2
  rcases h7 with ⟨n2, hn2⟩

  use fun i j =>
    match i, j with
    | 0, 0 => (⌊a 0 0⌋ : ℤ)
    | 0, 1 => (⌊a 0 1⌋ : ℤ)
    | 0, 2 => m0 - ⌊a 0 0⌋ - ⌊a 0 1⌋
    | 1, 0 => (⌊a 1 0⌋ : ℤ)
    | 1, 1 => (⌊a 1 1⌋ : ℤ)
    | 1, 2 => m1 - ⌊a 1 0⌋ - ⌊a 1 1⌋
    | 2, 0 => n0 - ⌊a 0 0⌋ - ⌊a 1 0⌋
    | 2, 1 => n1 - ⌊a 0 1⌋ - ⌊a 1 1⌋
    | 2, 2 => m2 - (n0 - ⌊a 0 0⌋ - ⌊a 1 0⌋) - (n1 - ⌊a 0 1⌋ - ⌊a 1 1⌋)
    | _ , _ => 0

  constructor
  · -- Show that the sum of each row is equal
    intro i
    fin_cases i <;> simp [Fin.sum_univ_three, add_assoc]
    all_goals
      norm_num [add_assoc] at *
      all_goals linarith
  · -- Show that the sum of each column is equal
    intro j
    fin_cases j <;> simp [Fin.sum_univ_three, add_assoc]
    all_goals
      norm_num [add_assoc] at *
      all_goals linarith