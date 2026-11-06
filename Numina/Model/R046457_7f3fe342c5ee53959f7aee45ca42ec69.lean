import Mathlib

theorem number_theory_15039 : IsLeast {n : ℕ | ∃ a : Fin 4 → ℕ, (∀ i, (Nat.digits 10 (a i)).length = 2) ∧
    a 0 = 57 ∧ a 1 = 13 ∧ a 2 = 72 ∧ ∑ i, (Nat.digits 10 (a i)).sum = (5⁻¹ : ℚ) * ∑ i, a i ∧
    n = a 3} 38 := by 
  constructor 
  · -- Show that 38 is indeed possible
    use λ i => match i with
      | 0 => 57
      | 1 => 13
      | 2 => 72
      | 3 => 38
      | _ => 0 -- This case won't happen, but needed to satisfy Fin 4
    constructor
    · intro i
      fin_cases i <;> simp 
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · native_decide
    · rfl
  · -- Show that 38 is the smallest
    intro n hn
    rcases hn with ⟨a, ha1, ha0, ha1', ha2, hsum, hn⟩
    have h0 := ha1 0
    have h1 := ha1 1
    have h2 := ha1 2
    have h3 := ha1 3
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ha0, ha1', ha2] at hsum hn
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ha0, ha1', ha2] at hsum hn 
    have h4 : a 3 ≥ 38 := by 
      by_contra h
      push_neg at h
      have h4 : a 3 < 38 := by linarith 
      interval_cases h4 : a 3 <;> norm_num [h4] at hsum h0 h1 h2 h3 hn
      <;> omega 
    linarith [hn, h4]