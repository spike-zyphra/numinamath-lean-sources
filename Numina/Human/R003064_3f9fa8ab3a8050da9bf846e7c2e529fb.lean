import Mathlib

theorem algebra_150149 :
    IsLeast {n : ℕ | ∃ a b c d : ℕ, a * b + b * c + c * d + d * a = 707 ∧ n = a + b + c + d} 108 := by
  constructor
  · -- Let's prove 108 is in the set
    use 7, 101, 0, 0
    all_goals norm_num
  · -- Now we prove that 108 is a lower bound
    intro n hn
    rcases hn with ⟨a, b, c, d, h_eq, h_sum⟩
    have h1 : (a + c) * (b + d) = 707 := by
      nlinarith [h_eq]
    by_contra h
    push_neg at h
    have h2 : n = a + b + c + d := by linarith
    have h3 : a + c + b + d ≥ 108 := by
      have : (a + c) = 1 ∨ (a + c) = 7 ∨ (a + c) = 101 ∨ (a + c) = 707 := by
        have h4 : (a + c) ≤ 707 := by nlinarith
        interval_cases (a + c) <;> omega
      rcases this with (hac | hac | hac | hac)
      · -- Case a + c = 1
        have hbd : b + d = 707 := by 
          rw [hac] at h1
          nlinarith
        linarith [hbd, hac]
      · -- Case a + c = 7
        have hbd : b + d = 101 := by 
          rw [hac] at h1
          nlinarith
        linarith [hbd, hac]
      · -- Case a + c = 101
        have hbd : b + d = 7 := by 
          rw [hac] at h1
          nlinarith
        linarith [hbd, hac]
      · -- Case a + c = 707
        have hbd : b + d = 1 := by 
          rw [hac] at h1
          nlinarith
        linarith [hbd, hac]
    linarith [h2, h3]