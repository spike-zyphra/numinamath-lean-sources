import Mathlib

theorem algebra_317602 :
  IsGreatest {x : ℤ | ∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c = 518 ∧ a * b - a * c = 360 ∧ x = a * b * c} 1008 := by
  constructor
  · -- First, show that 1008 is in the set.
    use 72, 7, 2
    norm_num
  · -- Now, prove that no larger value is in the set.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, hx⟩
    have h3 : c * (a + b) = 158 := by
      nlinarith
    have h4 : c ∣ 158 := by
      use a + b
      all_goals linarith
    have h5 : c = 1 ∨ c = 2 ∨ c = 79 ∨ c = 158 := by
      have h6 : c ∣ 158 := h4
      have h7 : c > 0 := hc
      have h8 : c ≤ 158 := by
        apply Int.le_of_dvd (by norm_num) h6
      interval_cases c <;> norm_num at h6
      <;> try { tauto }
    rcases h5 with h5 | h5 | h5 | h5
    · -- Case c = 1
      rw [h5] at h3 h1 h2
      have h8 : a + b = 158 := by
        nlinarith
      have h9 : a * b = 518 - b := by
        nlinarith
      rw [show a = 158 - b by nlinarith] at h9
      nlinarith [sq_nonneg (b - 74 : ℤ), sq_nonneg (b - 7 : ℤ), sq_nonneg (b * 1 : ℤ), sq_nonneg ((158 - b) * 1 : ℤ)]
    · -- Case c = 2
      rw [h5] at h3 h1 h2 hx
      have h8 : a + b = 79 := by
        nlinarith
      have h9 : a * b = 518 - 2 * b := by
        nlinarith
      have h10 : b = 74 ∨ b = 7 := by
        have h11 : b ^ 2 - 81 * b + 518 = 0 := by
          rw [show a = 79 - b by nlinarith] at h9
          nlinarith
        have h12 : (b - 74) * (b - 7) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h12) with h13 h14
        · -- b - 74 = 0
          left
          linarith
        · -- b - 7 = 0
          right
          linarith
      rcases h10 with h10 | h10
      · -- b = 74
        have h11 : a = 5 := by 
          nlinarith
        nlinarith
      · -- b = 7
        have h11 : a = 72 := by 
          nlinarith
        nlinarith
    · -- Case c = 79
      rw [h5] at h3 h1 h2
      have h8 : a + b = 2 := by
        nlinarith
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 1 : ℤ)]
    · -- Case c = 158
      rw [h5] at h3 h1 h2
      have h8 : a + b = 1 := by 
        nlinarith
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 1 : ℤ)]