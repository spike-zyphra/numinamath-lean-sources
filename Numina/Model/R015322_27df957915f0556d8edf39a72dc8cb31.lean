import Mathlib

theorem number_theory_2542 {a : ℕ} (ha : IsGreatest {x | 0 < x ∧ 64 % x = 4 ∧ 155 % x = 5 ∧ 187 % x = 7} a) :
    a = 25 ∨ a = 30 ∨ a = 35 := by

  have h1 : a ∈ {x | 0 < x ∧ 64 % x = 4 ∧ 155 % x = 5 ∧ 187 % x = 7} := by
    exact ha.1
  rcases h1 with ⟨ha_pos, ha1, ha2, ha3⟩
  have h2 : ∀ x, x ∈ {x | 0 < x ∧ 64 % x = 4 ∧ 155 % x = 5 ∧ 187 % x = 7} → x ≤ a := by 
    apply ha.2
  have h3 : (30 : ℕ) ∈ {x | 0 < x ∧ 64 % x = 4 ∧ 155 % x = 5 ∧ 187 % x = 7} := by
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  have h30 : 30 ≤ a := by
    specialize h2 30 h3
    linarith
  have h25 : a ≤ 64 := by
    by_contra h
    push_neg at h
    have h4 : 64 % a = 4 := ha1
    have h5 : a > 64 := h
    have h6 : 64 % a = 64 := by
      rw [Nat.mod_eq_of_lt]
      all_goals
      omega
    omega
  interval_cases a <;> norm_num at ha1 ha2 ha3 h30 ⊢ <;> omega