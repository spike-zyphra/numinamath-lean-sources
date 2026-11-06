import Mathlib

theorem number_theory_320382 :
    IsLeast {n | ∃ k, n = k + (k+1) + (k+2) + (k+3) + (k+4) + (k+5) + (k+6) + (k+7) + (k+8) ∧
      ∃ m, n = m + (m+1) + (m+2) + (m+3) + (m+4) + (m+5) + (m+6) + (m+7) + (m+8) + (m+9) ∧
      ∃ p, n = p + (p+1) + (p+2) + (p+3) + (p+4) + (p+5) + (p+6) + (p+7) + (p+8) + (p+9) + (p+10)} 495 := by
  constructor
  · -- First part: show 495 is in the set
    use 51
    constructor
    · -- Show that 495 can be expressed as the sum of 9 consecutive integers
      norm_num
    · -- Second part: show there exists m
      existsi 45
      constructor
      · -- Show that 495 can be expressed as the sum of 10 consecutive integers
        norm_num
      · -- Third part: show there exists p
        existsi 40
        all_goals norm_num
  · -- Second part: show that 495 is the smallest
    intro n hn
    rcases hn with ⟨k, hk, ⟨m, hm, ⟨p, hp⟩⟩⟩
    omega