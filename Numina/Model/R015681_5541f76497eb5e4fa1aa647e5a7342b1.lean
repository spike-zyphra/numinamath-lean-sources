import Mathlib

open Real Set
open scoped Real

theorem inequalities_130909 (x y : ℝ) :
  cos (x ^ 2) + cos (y ^ 2) - cos (x * y) < 3 := by
  have h11 : cos (x ^ 2) ≤ 1 := by
    apply cos_le_one
  have h22 : cos (y ^ 2) ≤ 1 := by
    apply cos_le_one
  have h33 : cos (x * y) ≥ -1 := by
    linarith [neg_one_le_cos (x * y)]
  have h4 : cos (x ^ 2) + cos (y ^ 2) - cos (x * y) ≤ 3 := by
    nlinarith
  by_contra h
  push_neg at h
  have h11 : cos (x ^ 2) = 1 := by
    nlinarith [cos_le_one (x ^ 2), cos_le_one (y ^ 2), neg_one_le_cos (x * y)]
  have h22 : cos (y ^ 2) = 1 := by
    nlinarith [cos_le_one (x ^ 2), cos_le_one (y ^ 2), neg_one_le_cos (x * y)]
  have h33 : cos (x * y) = -1 := by
    nlinarith [cos_le_one (x ^ 2), cos_le_one (y ^ 2), neg_one_le_cos (x * y)]
  have h5 : ∃ k : ℤ, x ^ 2 = 2 * k * Real.pi := by
    rw [cos_eq_one_iff] at h11
    rcases h11 with ⟨k, hk⟩
    use k
    linarith
  have h6 : ∃ m : ℤ, y ^ 2 = 2 * m * Real.pi := by
    rw [cos_eq_one_iff] at h22
    rcases h22 with ⟨m, hm⟩
    use m
    linarith
  have h7 : ∃ n : ℤ, x * y = (2 * n + 1) * Real.pi := by
    rw [cos_eq_neg_one_iff] at h33
    rcases h33 with ⟨n, hn⟩
    use n
    linarith
  rcases h5 with ⟨k, hk⟩
  rcases h6 with ⟨m, hm⟩
  rcases h7 with ⟨n, hn⟩
  have h9 : x ^ 2 = 2 * (k : ℝ) * Real.pi := by linarith
  have h10 : y ^ 2 = 2 * (m : ℝ) * Real.pi := by linarith
  have h11 : x * y = (2 * (n : ℝ) + 1) * Real.pi := by linarith
  have h12 : (x * y) ^ 2 = x^2 * (y ^ 2) := by ring
  have h13 : (x * y) ^ 2 = ((2 * (n : ℝ) + 1) * Real.pi) ^ 2 := by
    rw [show x * y = (2 * (n : ℝ) + 1) * Real.pi by linarith [h11]]
  have h14 : x ^ 2 * (y ^ 2) = (4 * ((k : ℝ) * (m : ℝ)) * Real.pi ^ 2) := by
    rw [h9, h10]
    nlinarith [Real.pi_pos]
  have h17 : 4 * ((k : ℝ) * (m : ℝ)) * Real.pi ^ 2 = ((2 * (n : ℝ) + 1) * Real.pi) ^ 2 := by
    have h18 : x^2 * (y ^ 2) = ((2 * (n : ℝ) + 1) * Real.pi) ^ 2 := by
      have h19 : x^2 * (y ^ 2) = (x * y) ^ 2 := by ring
      rw [h19]
      all_goals
        rw [h13]
    nlinarith [h14, h18]
  have h90 : (4 * ((k : ℝ) * (m : ℝ)) ) = (2 * (n : ℝ) + 1) ^ 2 := by
    have h91 : Real.pi ^ 2 > 0 := by
      positivity
    have h92 : 4 * ((k : ℝ) * (m : ℝ)) * Real.pi ^ 2 = ((2 * (n : ℝ) + 1) * Real.pi) ^ 2 := h17
    have h93 : (4 * ((k : ℝ) * (m : ℝ)) ) = (2 * (n : ℝ) + 1) ^ 2 := by
      have h94 : Real.pi ^ 2 > 0 := by positivity
      apply (mul_left_inj' (ne_of_gt h94)).mp
      nlinarith
    linarith
  have h34 : (4 * ((k : ℤ) * (m : ℤ)) : ℤ) = (2 * (n : ℤ) + 1) ^ 2 := by
    have h35 : (4 * ((k : ℝ) * (m : ℝ)) ) = (2 * (n : ℝ) + 1) ^ 2 := h90
    norm_cast at h35 ⊢
  have h37 : (4 * ((k : ℤ) * (m : ℤ)) : ℤ) % 2 = 0 := by
    omega
  have h38 : ((2 * (n : ℤ) + 1) ^ 2 : ℤ) % 2 = 1 := by
    have h171 : ((2 * (n : ℤ) + 1) ^ 2 : ℤ) % 2 = 1 := by
      have h92 : (2 * (n : ℤ) + 1) % 2 = 1 := by omega
      simp [pow_two, Int.add_emod, Int.mul_emod, h92]
    omega
  omega