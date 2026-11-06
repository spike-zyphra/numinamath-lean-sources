import Mathlib

theorem number_theory_300127 (a b c : ℤ) (h : (a - b)^10 + (a - c)^10 = 1) :
    abs (a - b) + abs (b - c) + abs (c - a) = 2 := by
  have h1 : (a - b) ^ 10 ≤ 1 := by linarith [show 0 ≤ (a - c) ^ 10 by positivity, h]
  have h2 : (a - c) ^ 10 ≤ 1 := by linarith [show 0 ≤ (a - b) ^ 10 by positivity, h]
  have h3 : (a - b) ^ 10 ≥ 0 := by positivity
  have h4 : (a - c) ^ 10 ≥ 0 := by positivity
  have h5 : (a - b) ^ 10 = 0 ∨ (a - b) ^ 10 = 1 := by
    have h51 : (a - b) ^ 10 ≤ 1 := h1
    have h52 : (a - b) ^ 10 ≥ 0 := h3
    have h53 : (a - b) ^ 10 ≤ 1 := by linarith
    have : (a - b) ^ 10 = 0 ∨ (a - b) ^ 10 = 1 := by omega
    assumption
  have h6 : (a - c) ^ 10 = 0 ∨ (a - c) ^ 10 = 1 := by
    have h61 : (a - c) ^ 10 ≤ 1 := h2
    have h62 : (a - c) ^ 10 ≥ 0 := h4
    have h63 : (a - c) ^ 10 ≤ 1 := by linarith
    have : (a - c) ^ 10 = 0 ∨ (a - c) ^ 10 = 1 := by omega
    assumption
  cases h5 with
  | inl h5' =>
    have h6' : (a - c) ^ 10 = 1 := by
      omega
    have h7 : a - b = 0 := by
      have h8 : (a - b) ^ 10 = 0 := h5'
      have : a - b = 0 := by
        have h10 : (a - b) ^ 10 = 0 := h8
        simp at h10
        linarith
      assumption
    have h8 : (a - c) ^ 2 = 1 := by
      have h8' : (a - c) ^ 10 = 1 := h6'
      have h8'' : (a - c) ^ 2 = 1 := by
        have h9 : (a - c) ^ 10 - 1 = 0 := by omega
        have h10 : (a - c) ^ 10 - 1 = ((a - c) ^ 2 - 1) * ((a - c) ^ 8 + (a - c) ^ 6 + (a - c) ^ 4 + (a - c) ^ 2 + 1) := by ring
        rw [h10] at h9
        have h11 : (a - c) ^ 2 - 1 = 0 ∨ ((a - c) ^ 8 + (a - c) ^ 6 + (a - c) ^ 4 + (a - c) ^ 2 + 1) = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero at h9
          assumption
        cases h11 with
        | inl h12 =>
          linarith
        | inr h13 =>
          have h14 : (a - c) ^ 8 + (a - c) ^ 6 + (a - c) ^ 4 + (a - c) ^ 2 + 1 > 0 := by
            positivity
          have h15 : (a - c) ^ 8 + (a - c) ^ 6 + (a - c) ^ 4 + (a - c) ^ 2 + 1 = 0 := h13
          linarith
      assumption
    have h9 : a - c = 1 ∨ a - c = -1 := by
      have h8' : (a - c) ^ 2 = 1 := h8
      have : a - c = 1 ∨ a - c = -1 := by
        rw [sq_eq_one_iff] at h8'
        assumption
      assumption
    cases h9 with
    | inl h10 =>
      have h11 : b - c = 1 := by
        have h100 : a = b := by linarith [h7]
        have h102 : a - c = 1 := h10
        linarith [h100, h102]
      have h12 : abs (a - b) = 0 := by
        rw [h7]
        norm_num
      have h13 : abs (b - c) = 1 := by
        rw [h11]
        norm_num
      have h14 : abs (c - a) = 1 := by
        have h141 : c - a = -1 := by
          have h100 : a = b := by linarith [h7]
          linarith [h100, h11]
        rw [h141]
        norm_num
      linarith [h12, h13, h14]
    | inr h11 =>
      have h12 : b - c = -1 := by
        have h100 : a = b := by linarith [h7]
        have h102 : a - c = -1 := h11
        linarith [h100, h102]
      have h13 : abs (b - c) = 1 := by
        rw [h12]
        norm_num
      have h14 : abs (c - a) = 1 := by
        have h141 : c - a = 1 := by
          have h100 : a = b := by linarith [h7]
          linarith [h100, h12]
        rw [h141]
        norm_num
      have h12 : abs (a - b) = 0 := by
        rw [h7]
        norm_num
      linarith [h12, h13, h14]
  | inr h5' =>
    have h6' : (a - c) ^ 10 = 0 := by
      omega
    have h7 : a - c = 0 := by
      have h8 : (a - c) ^ 10 = 0 := h6'
      have : a - c = 0 := by
        have h8' : (a - c) ^ 10 = 0 := h8
        simp at h8'
        linarith
      assumption
    have h8 : (a - b) ^ 2 = 1 := by
      have h8' : (a - b) ^ 10 = 1 := h5'
      have h8'' : (a - b) ^ 2 = 1 := by
        have h9 : (a - b) ^ 10 - 1 = 0 := by omega
        have h10 : (a - b) ^ 10 - 1 = ((a - b) ^ 2 - 1) * ((a - b) ^ 8 + (a - b) ^ 6 + (a - b) ^ 4 + (a - b) ^ 2 + 1) := by ring
        rw [h10] at h9
        have h11 : (a - b) ^ 2 - 1 = 0 ∨ ((a - b) ^ 8 + (a - b) ^ 6 + (a - b) ^ 4 + (a - b) ^ 2 + 1) = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero at h9
          assumption
        cases h11 with
        | inl h12 =>
          linarith
        | inr h13 =>
          have h14 : (a - b) ^ 8 + (a - b) ^ 6 + (a - b) ^ 4 + (a - b) ^ 2 + 1 > 0 := by
            positivity
          have h15 : (a - b) ^ 8 + (a - b) ^ 6 + (a - b) ^ 4 + (a - b) ^ 2 + 1 = 0 := h13
          linarith
      assumption
    have h9 : a - b = 1 ∨ a - b = -1 := by
      have h8' : (a - b) ^ 2 = 1 := h8
      have : a - b = 1 ∨ a - b = -1 := by
        rw [sq_eq_one_iff] at h8'
        assumption
      assumption
    have h7' : abs (a - b) = 1 := by
      cases h9 with
      | inl h10 =>
        rw [h10]
        norm_num
      | inr h11 =>
        rw [h11]
        norm_num
    have h10 : abs (b - c) = 1 := by
      have h101 : b - c = -(a - b) := by
        have h100 : a - c = 0 := h7
        linarith [h100]
      rw [h101]
      rw [abs_neg]
      rw [h7']
    have h11 : abs (c - a) = 0 := by
      have h111 : c - a = 0 := by
        nlinarith [h7]
      rw [h111]
      norm_num
    linarith [h7', h10, h11]