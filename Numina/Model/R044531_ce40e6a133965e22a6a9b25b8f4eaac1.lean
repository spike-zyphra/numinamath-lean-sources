import Mathlib

theorem algebra_309258 {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (hsum : ∀ n, ∑ i in Finset.range n, a i = a 0 * (1 - r ^ n) / (1 - r)) (h10 : ∑ i in Finset.range 10, a i = 10)
    (h30 : ∑ i in Finset.range 30, a i = 70) :
    ∑ i in Finset.range 40, a i = 150 := by
  have h10' : a 0 * (1 - r ^ 10) / (1 - r) = 10 := by 
    rw [hsum 10] at h10
    simpa using h10
  have h30' : a 0 * (1 - r ^ 30) / (1 - r) = 70 := by 
    rw [hsum 30] at h30 
    simpa using h30 
  have eq1 : a 0 * (1 - r ^ 30) / (1 - r) = (a 0 * (1 - r ^ 10) / (1 - r)) * (1 + r ^ 10 + r ^ 20) := by 
    field_simp [(show 1 - r ≠ 0 from by 
      by_contra h
      have : r = 1 := by linarith 
      rw [this] at h10' 
      norm_num [h] at h10' 
      all_goals linarith 
    )]
    ring_nf 
  rw [eq1] at h30' 
  rw [h10'] at h30' 
  -- Let y = r^10, then (1 + y + y^2) = 7 => y^2 + y - 6 = 0
  -- discriminant: 1 + 24 = 25; roots: (-1 ± 5)/2 => 2 or -3
  -- So r^10 = 2 or r^10 = -3
  have h_eq2 : (r ^ 10 - 2) * (r ^ 10 + 3) = 0 := by 
    nlinarith 
  have h_eq3 : r ^ 10 - 2 = 0 ∨ r ^ 10 + 3 = 0 := by 
    cases (mul_eq_zero.mp h_eq2) with 
    | inl h => 
      left 
      linarith 
    | inr h => 
      right 
      linarith 
  cases h_eq3 with 
  | inl h_eq4 => 
    have h_eq5 : r ^ 10 = 2 := by linarith 
    have h40' : ∑ i in Finset.range 40, a i = a 0 * (1 - r ^ 40) / (1 - r) := by 
      rw [hsum 40] 
    have eq2 : a 0 * (1 - r ^ 40) / (1 - r) = (a 0 * (1 - r ^ 10) / (1 - r)) * (1 + r ^ 10 + r ^ 20 + r ^ 30) := by 
      field_simp [(show 1 - r ≠ 0 from by 
          by_contra h 
          have : r = 1 := by linarith 
          rw [this] at h10' 
          norm_num [h] at h10' 
          all_goals linarith 
      )]
      ring_nf 
    rw [h40']
    rw [eq2, h10', h_eq5]
    have h50 : r ^ 20 = 4 := by 
      have h_eq6 : r ^ 20 = (r ^ 10) ^ 2 := by ring 
      rw [h_eq6, h_eq5] 
      norm_num 
    have h60 : r ^ 30 = 8 := by 
      have h_eq7 : r ^ 30 = (r ^ 10) ^ 3 := by ring 
      rw [h_eq7, h_eq5] 
      norm_num 
    rw [h50, h60] 
    norm_num 
  | inr h_eq4 => 
    have h_eq5 : r ^ 10 = -3 := by linarith 
    nlinarith [sq_nonneg (r ^ 5), sq_nonneg (r ^ 2), sq_nonneg (r + 1), sq_nonneg (r - 1)]