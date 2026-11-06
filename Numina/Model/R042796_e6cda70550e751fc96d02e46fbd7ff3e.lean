import Mathlib

theorem number_theory_76503 (a : Fin 5 → ℕ) (ha : ∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) :
    IsLeast {x | ∃ a : Fin 5 → ℕ, (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧ x = ∑ i, a i} 4 := by
  constructor
  · -- Show 4 is in the set
    use λ i =>
      match i with
      | 0 => 0
      | 1 => 1
      | 2 => 1
      | 3 => 1
      | 4 => 1
    constructor
    · -- Show that any two distinct indices give coprime numbers
      intro i j hne
      fin_cases i <;> fin_cases j <;> simp at *
      <;> norm_num [Nat.Coprime] at *
    · -- Show that the sum equals 4
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  · -- Show 4 is the smallest element in the set
    intro x hk
    rcases hk with ⟨b, h1, hx⟩
    have h2 : x = ∑ i : Fin 5, b i := by
      simpa using hx
    have h3 : ∑ i : Fin 5, b i ≥ 4 := by
      have h4_0 : b 0 ≥ 0 := by omega
      have h4_1 : b 1 ≥ 0 := by omega
      have h4_2 : b 2 ≥ 0 := by omega
      have h4_3 : b 3 ≥ 0 := by omega
      have h4_4 : b 4 ≥ 0 := by omega
      have h5 : Nat.Coprime (b 0) (b 1) := h1 0 1 (by simp)
      have h5' : Nat.Coprime (b 0) (b 2) := h1 0 2 (by simp)
      have h5'' : Nat.Coprime (b 0) (b 3) := h1 0 3 (by simp)
      have h5''' : Nat.Coprime (b 0) (b 4) := h1 0 4 (by simp)
      have h6 : Nat.Coprime (b 1) (b 2) := h1 1 2 (by simp)
      have h6' : Nat.Coprime (b 1) (b 3) := h1 1 3 (by simp)
      have h6'' : Nat.Coprime (b 1) (b 4) := h1 1 4 (by simp)
      have h7 : Nat.Coprime (b 2) (b 3) := h1 2 3 (by simp)
      have h7' : Nat.Coprime (b 2) (b 4) := h1 2 4 (by simp)
      have h7'' : Nat.Coprime (b 3) (b 4) := h1 3 4 (by simp)
      have h8 : b 0 + b 1 + b 2 + b 3 + b 4 ≥ 4 := by
        by_contra h
        push_neg at h
        have h9 : b 0 + b 1 + b 2 + b 3 + b 4 < 4 := by linarith
        have h10 : b 0 ≤ 3 := by omega
        have h11 : b 1 ≤ 3 := by omega
        have h12 : b 2 ≤ 3 := by omega
        have h13 : b 3 ≤ 3 := by omega
        have h14 : b 4 ≤ 3 := by omega
        interval_cases b 0 <;> interval_cases b 1 <;> interval_cases b 2 <;> interval_cases b 3 <;> interval_cases b 4 <;> norm_num [Nat.Coprime] at h5 h5' h5'' h5''' h6 h6' h6'' h7 h7' h7'' ⊢ <;> omega
      have : ∑ i : Fin 5, b i = b 0 + b 1 + b 2 + b 3 + b 4 := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      linarith [h8, this]
    linarith [h2, h3]