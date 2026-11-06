import Mathlib

theorem algebra_21589 : 
  let triangular_number (n : ℕ) := n * (n + 1) / 2;
  IsLeast {b : ℕ | b > 2011 ∧ ∃ x : ℕ, x > 0 ∧ triangular_number (b + 1) - triangular_number b = triangular_number x} 2015 := by
  intro triangular_number
  constructor
  · constructor
    · norm_num
    · use 63
      all_goals norm_num [triangular_number]
  · intro b hb
    rcases hb with ⟨hb1, x, hx, h⟩
    by_contra h1
    push_neg at h1
    have h2 : b < 2015 := by linarith
    have h3 : b ≥ 0 := by omega 
    have h4 : b < 2015 := h2
    have eq1 : triangular_number (b + 1) - triangular_number b = b + 1 := by 
      simp [triangular_number]
      <;> ring_nf <;> omega
    have eq2 : b + 1 = triangular_number x := by 
      linarith [h, eq1]
    have eq3 : b + 1 = x * (x + 1) / 2 := by
      have eq4 : triangular_number x = x * (x + 1) / 2 := by
        simp [triangular_number]
      omega
    have h5 : x ≤ 63 := by
      by_contra h6
      push_neg at h6 
      have h7 : x * (x + 1) / 2 ≥ 64 * (64 + 1) / 2 := by
        have h8 : x ≥ 64 := by omega 
        have h9 : x * (x + 1) ≥ 64 * (64 + 1) := by
          have h10 : x ≥ 64 := by omega 
          have h11 : (x + 1) ≥ (64 + 1) := by omega 
          nlinarith [sq_nonneg (x - 64 : ℤ)]
        have h10 : x * (x + 1) ≥ 64 * (64 + 1) := h9 
        omega
      have h8 : b + 1 ≥ 2080 := by 
        omega
      omega 
    have h8 : x ≤ 63 := h5 
    interval_cases x <;> omega