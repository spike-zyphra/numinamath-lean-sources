import Mathlib

open Finset

theorem algebra_165772 {x y : ℕ} (hy : y > 0) (h : x * (x + 1) * (x + 2) * (x + 3) * (x + 4) = 420) :
    y * (y + 1) * (y + 2) * (y + 3) * (y + 4) = 20 ∨ y * (y + 1) * (y + 2) * (y + 3) * (y + 4) = 120 := by
  have h1 : x ≤ 7 := by
    by_contra h2
    push_neg at h2
    have h2' : x ≥ 8 := by omega
    have h3 : x * (x + 1) * (x + 2) * (x + 3) * (x + 4) ≥ 8 * 9 * 10 * 11 * 12 := by
      have h4 : x ≥ 8 := by linarith
      have h5 : x + 1 ≥ 9 := by omega
      have h6 : x + 2 ≥ 10 := by omega
      have h7 : x + 3 ≥ 11 := by omega
      have h8 : x + 4 ≥ 12 := by omega
      have h9 : x * (x + 1) * (x + 2) * (x + 3) * (x + 4) ≥ 8 * 9 * 10 * 11 * 12 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
      linarith
    norm_num at h3
    linarith
  have h_dec : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
  rcases h_dec with (r | r | r | r | r | r | r | r)
  · -- x = 0
    norm_num [r] at h
    all_goals omega
  · -- x = 1
    norm_num [r] at h
    all_goals omega
  · -- x = 2
    norm_num [r] at h
    all_goals omega
  · -- x = 3
    norm_num [r] at h
    all_goals omega
  · -- x = 4
    norm_num [r] at h
    all_goals omega
  · -- x = 5
    norm_num [r] at h
    all_goals omega
  · -- x = 6
    norm_num [r] at h
    all_goals omega
  · -- x = 7
    norm_num [r] at h
    all_goals omega