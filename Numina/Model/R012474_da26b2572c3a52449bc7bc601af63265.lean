import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12067 {f : ℝ → ℝ}
  (hf : ∀ x, f x = ((2 ^ x + 1) ^ 2) / (2 ^ x * x) + 1)
  (M N : ℝ)
  (hM : ∃ x ∈ Ico (-2018) 0, f x = M)
  (hN : ∃ x ∈ Ioc 0 2018, f x = N)
  (hMub : ∀ x ∈ Ico (-2018) 0, f x ≤ M)
  (hNlb : ∀ x ∈ Ioc 0 2018, f x ≥ N) :
  M + N = 2 := by 
  rcases hM with ⟨x, hx1, hx2⟩
  rcases hN with ⟨y, hy1, hy2⟩
  have h2 : -x ∈ Ioc (0 : ℝ) 2018 := by
    rcases hx1 with ⟨hx11, hx12⟩
    constructor
    · -- Show that 0 < -x
      linarith [hx12]
    · -- Show that -x ≤ 2018
      linarith [hx11]
  have h5 : f x = M := by linarith [hx2]
  have h6 : f (-x) ≥ N := by 
    apply hNlb
    exact h2
  have h10 : f (-x) + f x = 2 := by 
    have h12 : f (-x) - 2 = - (f x) := by
      rw [hf, hf]
      have h5 : (2 : ℝ) ^ (-x : ℝ) = 1 / (2 ^ (x : ℝ)) := by 
        rw [Real.rpow_neg]
        all_goals norm_num 
      rw [h5]
      field_simp [(show (2 : ℝ) ^ (x : ℝ) ≠ 0 by positivity), 
        show x ≠ 0 by 
          by_contra h
          rw [h] at hx1
          simp at hx1 
          all_goals linarith 
        , 
        show ( -x : ℝ ) ≠ 0 by 
          by_contra h
          have h' : x = 0 := by linarith 
          rw [h'] at hx1
          simp at hx1 
          all_goals linarith 
        ]
      <;> ring_nf 
      <;> field_simp 
      <;> ring_nf 
      <;> nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x]
    linarith 
  have h16 : N ≤ 2 - M := by 
    have h17 : f (-x) = 2 - f x := by linarith [h10] 
    rw [show f x = M by linarith [h5]] at h17 
    have h18 : f (-x) ≥ N := by linarith [h6] 
    linarith [h17, h18] 
  have h4 : -y ∈ Ico (-2018 : ℝ) (0 : ℝ) := by 
    rcases hy1 with ⟨hy11, hy12⟩
    constructor
    · -- Show that -2018 ≤ -y
      linarith [hy12]
    · -- Show that -y < 0
      linarith [hy11]
  have h7 : f (-y) ≤ M := by 
    apply hMub 
    exact h4 
  have h8 : f y = N := by linarith [hy2]
  have h12 : f (-y) + f y = 2 := by 
    have h13 : f (-y) - 2 = - (f y) := by
      rw [hf, hf]
      have h5 : (2 : ℝ) ^ (-y : ℝ) = 1 / (2 ^ (y : ℝ)) := by 
        rw [Real.rpow_neg]
        all_goals norm_num 
      rw [h5]
      field_simp [(show (2 : ℝ) ^ (y : ℝ) ≠ 0 by positivity), 
        show y ≠ 0 by 
          by_contra h
          rw [h] at hy1
          simp at hy1 
          all_goals linarith 
        , 
        show ( -y : ℝ ) ≠ 0 by 
          by_contra h
          have h' : y = 0 := by linarith 
          rw [h'] at hy1
          simp at hy1 
          all_goals linarith 
        ]
      <;> ring_nf 
      <;> field_simp 
      <;> ring_nf 
      <;> nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) y]
    linarith 
  have h18 : 2 - N ≤ M := by 
    have h17 : f (-y) = 2 - f y := by linarith [h12] 
    rw [show f y = N by linarith [h8]] at h17 
    have h16 : f (-y) ≤ M := by linarith [h7] 
    linarith [h17, h16] 
  linarith [h16, h18] 
  <;> ring_nf <;> linarith [h16, h18]
  <;> linarith 
  all_goals try { omega }
  all_goals try { nlinarith }