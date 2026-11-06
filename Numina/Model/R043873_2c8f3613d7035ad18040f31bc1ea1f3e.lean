import Mathlib

theorem algebra_20802 :
    IsLeast {n | ∃ k : Fin n → ℕ, (∀ i, k i ∈ Set.Ioo 0 49 ∧ IsSquare (k i)) ∧ 49 = ∑ i, k i} 3 := by
  constructor
  · -- Show 3 is in the set
    use λ i => match i with
      | 0 => 36
      | 1 => 9
      | 2 => 4
      | _ => 0
    constructor
    · -- Show that each element is in the set
      intro i
      fin_cases i <;> constructor <;> native_decide
    · -- Show the sum equals 49
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      <;> try native_decide
  · -- Show that 3 is the smallest element in the set
    intro n hn
    rcases hn with ⟨k, ⟨hk1, hk2⟩⟩
    by_contra h
    push_neg at h
    have h1 : n < 3 := h
    interval_cases n <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hk2 ⊢ 
      <;> try { 
        exfalso
        all_goals try { contradiction }
      }
      <;> try { 
        have h20 : k 0 ∈ Set.Ioo 0 49 := by
          have h := hk1 0
          exact h.1
        have h30 : IsSquare (k 0) := by 
          have h := hk1 0
          exact h.2
        have h21 : k 1 ∈ Set.Ioo 0 49 := by 
          have h := hk1 1
          exact h.1
        have h31 : IsSquare (k 1) := by
          have h := hk1 1
          exact h.2
        rcases h20 with ⟨h40, h50⟩
        rcases h21 with ⟨h41, h51⟩
        rcases h30 with ⟨r0, hr0⟩
        rcases h31 with ⟨r1, hr1⟩
        all_goals try { 
          have h_pos0 : r0 ^ 2 = k 0 := by
            linarith
          have h_pos1 : r1 ^ 2 = k 1 := by
            linarith
          have h200 : r0 ≤ 7 := by nlinarith
          have h201 : r0 > 0 := by nlinarith
          have h210 : r1 ≤ 7 := by nlinarith
          have h211 : r1 > 0 := by nlinarith
          interval_cases r0 <;> interval_cases r1 <;> omega
        }
      }