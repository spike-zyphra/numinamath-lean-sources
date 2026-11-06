import Mathlib

open Real Set

theorem algebra_106782 :
    IsLeast {x | ∃ a b : ℝ, x = max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2)} (3 / 4) := by
  constructor
  · -- Show that 3/4 is in the set.
    use 1 / 2, 1 / 2 
    norm_num [max_assoc, max_comm, max_left_comm]
  · -- Show that no smaller value is in the set.
    intro x hx 
    rcases hx with ⟨a, b, h_eq⟩
    by_contra h 
    push_neg at h 
    have h1 : max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) ≥ 3 / 4 := by
      by_contra h2 
      push_neg at h2 
      have h21 : a^2 + a * b + b^2 < 3 / 4 := by 
        have h3 : max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) < 3 / 4 := by 
          linarith [h2]
        have h4 : a^2 + a * b + b^2 ≤ max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) := by 
          simp [max_le_iff]
        nlinarith 
      have h22 : a^2 + a * (b - 1) + (b - 1)^2 < 3 / 4 := by 
        have h3 : max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) < 3 / 4 := by 
          linarith [h2]
        have h5 : a^2 + a * (b - 1) + (b - 1)^2 ≤ max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) := by 
          simp [max_le_iff]
        nlinarith 
      have h23 : (a - 1)^2 + (a - 1) * b + b^2 < 3 / 4 := by 
        have h3 : max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) < 3 / 4 := by 
          linarith [h2]
        have h6 : (a - 1)^2 + (a - 1) * b + b^2 ≤ max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) := by 
          simp [max_le_iff]
        nlinarith 
      have h24 : (a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2 < 3 / 4 := by 
        have h3 : max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) < 3 / 4 := by 
          linarith [h2]
        have h7 : (a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2 ≤ max (max (max (a^2 + a * b + b^2) (a^2 + a * (b - 1) + (b - 1)^2)) ((a - 1)^2 + (a - 1) * b + b^2)) ((a - 1)^2 + (a - 1) * (b - 1) + (b - 1)^2) := by 
          simp [max_le_iff]
        nlinarith 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), 
          sq_nonneg (a + b - 1), sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a), sq_nonneg (b)]
    linarith [h_eq, h1, h]