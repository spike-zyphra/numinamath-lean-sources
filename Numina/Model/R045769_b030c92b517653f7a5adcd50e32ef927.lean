import Mathlib

theorem algebra_13818 (S : Set (ℝ × ℝ)) (hS : S = {(x, y) : ℝ × ℝ | x > 0 ∧ y > 0 ∧ x + y = 35}) (x y : ℝ) (hxy : (x, y) ∈ S) :
  IsMaxOn (fun (x, y) => x ^ 5 * y ^ 2) S (x, y) → (x, y) = (25, 10) := by

  intro h_max 
  have h1 : x > 0 := by
    have h11 : (x, y) ∈ S := hxy
    rw [hS] at h11 
    simp at h11 ⊢
    all_goals try nlinarith
  have h2 : y > 0 := by
    have h11 : (x, y) ∈ S := hxy
    rw [hS] at h11 
    simp at h11 ⊢
    all_goals try nlinarith
  have h3 : x + y = 35 := by 
    have h11 : (x, y) ∈ S := hxy
    rw [hS] at h11 
    simp at h11 ⊢
    all_goals try nlinarith
  -- Now we need to compare with (25,10)

  have h4 : (25, 10) ∈ S := by 
    rw [hS]
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  have h5 : x ^ 5 * y ^ 2 ≥ (25 : ℝ) ^ 5 * (10 : ℝ) ^ 2 := by 
    have h6 : (x ^ 5 * y ^ 2) ≥ ((25 : ℝ) ^ 5 * (10 : ℝ) ^ 2) := by
      have h7 : (25, 10) ∈ S := h4
      have h8 : x ^ 5 * y ^ 2 ≥ (fun (p : ℝ × ℝ) => p.1 ^ 5 * p.2 ^ 2) (25, 10) := by 
        apply h_max
        exact h7
      simp at h8 ⊢
      all_goals try nlinarith
    linarith

  have h_eq : y = 35 - x := by 
    linarith
  rw [show y = 35 - x by linarith] at h5 
  have hx25 : x = 25 := by
    nlinarith [sq_nonneg (x - 25), sq_nonneg ((35 - x) - 10), sq_nonneg (x * (x - 25)), sq_nonneg ((35 - x) * (x - 25)), mul_pos h1 (show 0 < 35 - x by nlinarith), h5, sq_nonneg (x ^ 2 - 25 ^ 2), sq_nonneg ((35 - x) ^ 2 - 10 ^ 2)]
  -- Now using h_eq [hy10] to show (x,y) = (25,10).
  have hy10 : 35 - x = 10 := by
    nlinarith [show x = 25 by linarith]
  have hy10' : y = 10 := by
    linarith [show 35 - x = 10 by linarith, h_eq]
  simp [hx25, hy10']
  all_goals try linarith