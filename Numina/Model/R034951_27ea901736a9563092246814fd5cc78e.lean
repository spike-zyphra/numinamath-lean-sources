import Mathlib

theorem number_theory_259593 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ x = (15 * a + 16 * b)^2 ∧ ∃ c d : ℕ, c > 0 ∧ d > 0 ∧ x = (16 * a - 15 * b)^2} 231361 := by
  constructor
  · -- Show 231361 is in the set
    use 31, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    use 1, 1
    all_goals norm_num
  · -- Show no smaller element is in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx1, ⟨c, d, hc, hd, hx2⟩⟩
    by_contra h
    push_neg at h
    have h1 : (15 * a + 16 * b) ^ 2 = (16 * a - 15 * b) ^ 2 := by
      nlinarith [hx1, hx2]
    have h2 : 15 * a + 16 * b = 16 * a - 15 * b := by
      have h3 : (15 * a + 16 * b) ≤ (16 * a - 15 * b) := by
        nlinarith [show (15 * a + 16 * b) ^ 2 = (16 * a - 15 * b) ^ 2 from h1, show 0 ≤ (16 * a - 15 * b : ℕ) by nlinarith [show 0 ≤ (16 : ℕ) * a by nlinarith, show 0 ≤ (15 : ℕ) * b by nlinarith]]
      have h4 : (16 * a - 15 * b) ≤ (15 * a + 16 * b) := by
        nlinarith [show (15 * a + 16 * b) ^ 2 = (16 * a - 15 * b) ^ 2 from h1, show 0 ≤ (15 * a + 16 * b : ℕ) by nlinarith [show 0 ≤ (15 : ℕ) * a by nlinarith, show 0 ≤ (16 : ℕ) * b by nlinarith]]
      nlinarith
    have h3 : a = 31 * b := by
      omega
    have h4 : (15 * a + 16 * b) = 481 * b := by
      nlinarith [h3]
    have h6 : b < 1 := by
      by_contra h7
      push_neg at h7
      have h7 : b ≥ 1 := by linarith
      have h8 : (15 * a + 16 * b) ≥ 481 := by
        nlinarith [h3, h7]
      have h9 : (15 * a + 16 * b) ^ 2 ≥ 231361 := by
        nlinarith [show 0 ≤ (15 * a + 16 * b : ℕ) by nlinarith, h8]
      nlinarith [hx1, h9, h7]
    have h7 : b < 1 := by
      nlinarith
    have h8 : b = 0 := by
      omega
    omega