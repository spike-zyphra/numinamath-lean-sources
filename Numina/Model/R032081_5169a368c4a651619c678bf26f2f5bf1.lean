import Mathlib


open Nat


lemma lemma_1 (x : ℕ) (hx : 1 ≤ x) : 3 ^ x + 13 ^ x < 17 ^ x := by
  have h1 : x ≥ 1 := hx
  have h2 : ∀ (k : ℕ), 3 ^ (k + 1) + 13 ^ (k + 1) < 17 ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have h21 : 3 ^ (k + 1 + 1) + 13 ^ (k + 1 + 1) < 17 ^ (k + 1 + 1) := by
        have h11 : (3 : ℕ) ^ (k + 1 + 1) = 3 * (3 ^ (k + 1)) := by ring
        have h12 : (13 : ℕ) ^ (k + 1 + 1) = 13 * (13 ^ (k + 1)) := by ring
        have h13 : (17 : ℕ) ^ (k + 1 + 1) = 17 * (17 ^ (k + 1)) := by ring
        rw [h11, h12, h13]
        nlinarith [pow_pos (show (0 : ℕ) < 3 by norm_num) (k + 1), pow_pos (show (0 : ℕ) < 13 by norm_num) (k + 1), pow_pos (show (0 : ℕ) < 17 by norm_num) (k + 1), ih]
      simpa using h21
  have hx2 : x = (x - 1) + 1 := by
    omega
  rw [show x = (x - 1) + 1 by omega]
  exact h2 (x - 1)


theorem algebra_234280 {s t : ℕ} (h1 : 3^s + 13^t = 17^s) (h2 : 5^s + 7^t = 11^t) :
    s < t := by
  by_contra h
  push_neg at h
  have h3 : t ≤ s := by
    omega
  have h4 : 13 ^ t ≤ 13 ^ s := by
    apply pow_le_pow_right
    all_goals
      omega
  have h5 : 3 ^ s + 13 ^ t ≤ 3 ^ s + 13 ^ s := by
    linarith [h4]
  have h6 : 3 ^ s + 13 ^ s < 17 ^ s := by
    have h7 : s ≥ 1 := by
      by_contra h8
      push_neg at h8
      have : s = 0 := by
        omega
      rw [this] at h1
      norm_num at h1
      all_goals
        omega
    apply lemma_1 s h7
  linarith