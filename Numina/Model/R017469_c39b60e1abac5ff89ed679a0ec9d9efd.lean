import Mathlib

theorem algebra_171655 {m n : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hangle : Real.arctan m = 2 * Real.arctan n) (hmp : m = 4 * n) :
    m * n = 2 := by
  have h1 : m = 4 * n := hmp
  have h2 : Real.tan (Real.arctan m) = Real.tan (2 * Real.arctan n) := by 
    rw [hangle]
  have htan1 : Real.tan (Real.arctan m) = m := by
    rw [Real.tan_arctan]
  have htan2 : Real.tan (2 * Real.arctan n) = 2 * n / (1 - n ^ 2) := by
    have htan : Real.tan (2 * Real.arctan n) = 2 * Real.tan (Real.arctan n) / (1 - Real.tan (Real.arctan n) ^ 2) := by
      rw [Real.tan_two_mul]
    have htan2 : Real.tan (Real.arctan n) = n := by
      rw [Real.tan_arctan]
    rw [htan2] at htan
    rw [htan]
    <;> ring_nf
    <;> field_simp [(show (1 : ℝ) - n^2 ≠ 0 by
      by_contra h
      have hn1 : n ^ 2 = 1 := by linarith
      have hn2 : n = 1 ∨ n = -1 := by
        rw [sq_eq_one_iff] at hn1
        tauto
      cases hn2 with
      | inl h => 
        rw [h] at h2
        norm_num at h2
        all_goals linarith [hm, h1]
      | inr h => 
        rw [h] at h2
        norm_num at h2
        all_goals linarith [hm, h1]
    )
    ]
    <;> linarith
  rw [htan1, htan2] at h2
  rw [h1] at h2
  have h5 : 2 * n * (1 - 2 * n ^ 2) = 0 := by
    have hne : 1 - n ^ 2 ≠ 0 := by
      by_contra h
      have hn1 : n ^ 2 = 1 := by linarith
      have hn2 : n = 1 ∨ n = -1 := by 
        rw [sq_eq_one_iff] at hn1
        tauto
      cases hn2 with
      | inl h => 
        rw [h] at h2
        norm_num at h2
        all_goals nlinarith [hm, h1]
      | inr h => 
        rw [h] at h2
        norm_num at h2
        all_goals nlinarith [hm, h1]
    have ht2 : 4 * n * (1 - n ^ 2) = 2 * n := by
      field_simp [hne] at h2 ⊢
      nlinarith
    nlinarith
  have h5' : 1 - 2 * n ^ 2 = 0 := by
    cases (mul_eq_zero.mp h5) with
    | inl h5 => 
      exfalso
      apply hn
      linarith
    | inr h5 => 
      linarith
  have h7 : n ^ 2 = 1 / 2 := by
    nlinarith
  have h8 : m * n = 4 * (n ^ 2) := by
    rw [h1]
    linarith
  nlinarith