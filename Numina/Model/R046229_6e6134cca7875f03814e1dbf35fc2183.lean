import Mathlib


theorem algebra_607798 : (IsLeast {x : ℤ | ∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ∧ a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c > 0} 4)
 ∧ {(a, b, c) : ℤ × ℤ × ℤ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = 4} = {(1 ,1 ,2), (1, 2, 1), (2, 1, 1)} := by 
  constructor
  · constructor
    · -- Show 4 is in the set
      use 1, 1, 2
      all_goals norm_num
    · -- Show 4 is the minimum
      intro x hx
      rcases hx with ⟨a, b, c, ha, hb, hc, hx_eq, hx_pos⟩
      have h1 : a ≥ 1 := by linarith
      have h2 : b ≥ 1 := by linarith
      have h3 : c ≥ 1 := by linarith
      by_contra h
      push_neg at h
      have h2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c < 4 := by linarith
      have h4 : a ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h10 : a ≥ 3 := by linarith
        have h11 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 6 := by
          have h8 : b ≥ 1 := by linarith
          have h9 : c ≥ 1 := by linarith
          have h101 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) := by
            ring
          rw [h101]
          have h102 : a + b + c ≥ 5 := by
            nlinarith
          have h103 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c ≥ 1 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos (show 0 < (1 : ℤ) by linarith) (show 0 < (1 : ℤ) by linarith)]
          nlinarith
        linarith
      have h5 : b ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h10 : b ≥ 3 := by linarith
        have h11 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 6 := by
          have h8 : a ≥ 1 := by linarith
          have h9 : c ≥ 1 := by linarith
          have h101 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) := by
            ring
          rw [h101]
          have h102 : a + b + c ≥ 5 := by
            nlinarith
          have h103 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c ≥ 1 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos (show 0 < (1 : ℤ) by linarith) (show 0 < (1 : ℤ) by linarith)]
          nlinarith
        linarith
      have h6 : c ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h10 : c ≥ 3 := by linarith
        have h11 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 6 := by
          have h8 : a ≥ 1 := by linarith
          have h9 : b ≥ 1 := by linarith
          have h101 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) := by
            ring
          rw [h101]
          have h102 : a + b + c ≥ 5 := by
            nlinarith
          have h103 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c ≥ 1 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos (show 0 < (1 : ℤ) by linarith) (show 0 < (1 : ℤ) by linarith)]
          nlinarith
        linarith
      interval_cases a <;> interval_cases b <;> interval_cases c
      <;> omega
  · -- Show the set of triples is exactly these
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- Forward implication
      rintro ⟨ha, hb, hc, heq⟩
      have h1 : a ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h10 : a ≥ 3 := by linarith
        have h4 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 6 := by
          have h8 : b ≥ 1 := by linarith
          have h9 : c ≥ 1 := by linarith
          have h101 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) := by
            ring
          rw [h101]
          have h102 : a + b + c ≥ 5 := by
            nlinarith
          have h103 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c ≥ 1 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos (show 0 < (1 : ℤ) by linarith) (show 0 < (1 : ℤ) by linarith)]
          nlinarith
        nlinarith
      have h2 : b ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h10 : b ≥ 3 := by linarith
        have h4 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 6 := by
          have h8 : a ≥ 1 := by linarith
          have h9 : c ≥ 1 := by linarith
          have h101 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) := by
            ring
          rw [h101]
          have h102 : a + b + c ≥ 5 := by
            nlinarith
          have h103 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c ≥ 1 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos (show 0 < (1 : ℤ) by linarith) (show 0 < (1 : ℤ) by linarith)]
          nlinarith
        nlinarith
      have h3 : c ≤ 2 := by
        by_contra h5
        push_neg at h5
        have h10 : c ≥ 3 := by linarith
        have h4 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c ≥ 6 := by
          have h8 : a ≥ 1 := by linarith
          have h9 : b ≥ 1 := by linarith
          have h101 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) := by
            ring
          rw [h101]
          have h102 : a + b + c ≥ 5 := by
            nlinarith
          have h103 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c ≥ 1 := by
            nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              mul_pos (show 0 < (1 : ℤ) by linarith) (show 0 < (1 : ℤ) by linarith)]
          nlinarith
        nlinarith
      interval_cases a <;> interval_cases b <;> interval_cases c
      <;> norm_num at heq ⊢
      <;> tauto
    · -- Backward implication
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- Check (1, 1, 2)
        norm_num
      · -- Check (1, 2, 1)
        norm_num
      · -- Check (2, 1, 1)
        norm_num