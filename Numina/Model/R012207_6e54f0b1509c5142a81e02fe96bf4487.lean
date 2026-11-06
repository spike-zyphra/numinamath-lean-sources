import Mathlib
open Real
theorem algebra_190032 {a : ℕ → ℝ} {d : ℝ} (h : ∀ n, a n = a 0 + d * n) (hpos : ∀ n, 8 * ∑ i ∈ Finset.range n, a i + 2 * n ≥ 0)
    (hd : d > 0) (hs : ∀ n, Real.sqrt (8 * ∑ i ∈ Finset.range n, a i + 2 * n) = d * n) :
    ∀ n, a n = 4 * n + 7 / 4 := by

  have eq1 := hs 1
  have h1 : 8 * ∑ i ∈ Finset.range 1, a i + 2 * (1 : ℕ) = 8 * a 0 + 2 := by
    simp [Finset.sum_range_succ]

  have eq1' : Real.sqrt (8 * a 0 + 2) = d := by
    rw [h1] at eq1
    norm_num at eq1 ⊢
    simpa using eq1

  have eq1_eq : 8 * a 0 + 2 = d ^ 2 := by
    calc
      8 * a 0 + 2 = (Real.sqrt (8 * a 0 + 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        have h_nonneg := hpos 1
        norm_num at h_nonneg ⊢
        linarith
      _ = (d) ^ 2 := by
        rw [eq1']
      _ = d ^ 2 := by
        ring

  have eq2 := hs 2

  have h2_sum : 8 * ∑ i ∈ Finset.range 2, a i + 2 * (2 : ℕ) = 8 * (a 0 + (a 0 + d)) + 4 := by
    have ha1 : a 1 = a 0 + d := by
      specialize h 1
      norm_num at h ⊢
      linarith
    simp [Finset.sum_range_succ, ha1]
    all_goals linarith

  have eq2' : Real.sqrt (8 * (a 0 + (a 0 + d)) + 4) = 2 * d := by 
    have eq3 : Real.sqrt (8 * ∑ i ∈ Finset.range 2, a i + 2 * (2 : ℕ)) = d * 2 := by 
      simpa using eq2
    have eq3' : Real.sqrt (8 * ∑ i ∈ Finset.range 2, a i + 2 * (2 : ℕ)) = Real.sqrt (8 * (a 0 + (a 0 + d)) + 4) := by 
      rw [h2_sum]
    rw [eq3'] at eq3
    have : d * 2 = (2 * d : ℝ) := by ring
    rw [this] at eq3
    linarith

  have eq2_eq : 8 * (a 0 + (a 0 + d)) + 4 = 4 * d ^ 2 := by 
    calc
      8 * (a 0 + (a 0 + d)) + 4 = (Real.sqrt (8 * (a 0 + (a 0 + d)) + 4)) ^ 2 := by 
        rw [Real.sq_sqrt]
        have h_nonneg2 : 8 * (a 0 + (a 0 + d)) + 4 ≥ 0 := by 
          have h_nonneg := hpos 2
          have eq2_sum' : 8 * ∑ i ∈ Finset.range 2, a i + 2 * ↑2 = 8 * (a 0 + (a 0 + d)) + 4 := by 
            have ha1 : a 1 = a 0 + d := by
              specialize h 1
              norm_num at h ⊢
              linarith
            simp [Finset.sum_range_succ, ha1]
            all_goals linarith
          nlinarith [h_nonneg, eq2_sum']
        linarith
      _ = (2 * d) ^ 2 := by 
        rw [eq2']
      _ = 4 * d ^ 2 := by 
        ring

  have h_eq1 : d ^ 2 = 8 * a 0 + 2 := by linarith

  have h_eq2 : 4 * d ^ 2 = 16 * a 0 + 8 * d + 4 := by 
    linarith

  have h_eq3 : d - 2 * a 0 = 1 / 2 := by 
    nlinarith

  have h_eq4 : d = 4 := by 
    have h_eq5 : (d - 4) * (d) = 0 := by
      nlinarith [sq_nonneg (d - 4), sq_nonneg (a 0 + 1 / 4), hd]
    cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
    · -- `d - 4 = 0` so $d = 4$.
      linarith
    · -- `d = 0` which is impossible
      nlinarith

  have h_eq5 : a 0 = 7 / 4 := by 
    nlinarith

  intro n 
  have eq6 : a n = a 0 + d * (n : ℝ) := by 
    specialize h n 
    simpa using h

  rw [eq6]
  rw [h_eq5, h_eq4]
  all_goals ring