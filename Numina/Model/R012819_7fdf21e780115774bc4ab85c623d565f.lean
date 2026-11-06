import Mathlib

open BigOperators Real Set

lemma lemma_1 (a b c : ℝ) (h : ∀ x : ℝ, a * cos x + b * cos (2 * x) + c * cos (3 * x) ≥ -1) :
    |c| ≤ 1 := by
  have h1 := h 0
  have h2 := h (Real.pi)
  have h3 := h (Real.pi / 2)
  have h4 := h (Real.pi / 3)
  have h5 := h (2 * Real.pi / 3)
  have h1' : a + b + c ≥ -1 := by
    simp [Real.cos_zero, mul_add, mul_comm] at h1
    linarith
  have h2' : -a + b - c ≥ -1 := by
    have hp1 : Real.cos (Real.pi) = -1 := Real.cos_pi
    have hp2 : Real.cos (2 * Real.pi) = 1 := by
      have h' : 2 * Real.pi = 2 * Real.pi := rfl
      rw [h']
      exact Real.cos_two_pi
    have hp3 : Real.cos (3 * Real.pi) = -1 := by
      have h' : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
      rw [h']
      have : Real.cos (Real.pi + 2 * Real.pi) = Real.cos Real.pi := by
        rw [Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
        norm_num
      rw [this, Real.cos_pi]
      all_goals norm_num
    simp [hp1, hp2, hp3] at h2
    linarith
  have h3' : b ≤ 1 := by
    have hp1 : Real.cos (Real.pi / 2) = 0 := by
      exact Real.cos_pi_div_two
    have hp2 : Real.cos (2 * (Real.pi / 2)) = -1 := by
      have h' : 2 * (Real.pi / 2) = Real.pi := by ring
      rw [h']
      exact Real.cos_pi
    have hp3 : Real.cos (3 * (Real.pi / 2)) = 0 := by
      have h' : 3 * (Real.pi / 2) = Real.pi / 2 + Real.pi := by ring
      rw [h']
      have : Real.cos (Real.pi / 2 + Real.pi) = 0 := by
        rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
        norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
      linarith
    simp [hp1, hp2, hp3] at h3
    linarith
  have h4' : (a / 2) - (b / 2) - c ≥ -1 := by
    have hp1 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have hp2 : Real.cos (2 * (Real.pi / 3)) = -1 / 2 := by
      have h' : 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
      rw [h']
      rw [Real.cos_pi_sub]
      norm_num
    have hp3 : Real.cos (3 * (Real.pi / 3)) = -1 := by
      have h' : 3 * (Real.pi / 3) = Real.pi := by ring
      rw [h']
      exact Real.cos_pi
    simp [hp1, hp2, hp3] at h4
    linarith
  have h5' : - (a / 2) - (b / 2) + c ≥ -1 := by
    have hp1 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      have h' : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [h']
      rw [Real.cos_pi_sub]
      norm_num
    have hp2 : Real.cos (2 * (2 * Real.pi / 3)) = -1 / 2 := by
      have h1 : 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 := by ring
      rw [h1]
      have hp21 : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
        have hp22 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by ring
        rw [hp22]
        rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
        norm_num [Real.cos_pi_div_three, Real.sin_pi_div_three]
      exact hp21
    have hp3 : Real.cos (3 * (2 * Real.pi / 3)) = 1 := by
      have h' : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by ring
      rw [h']
      exact Real.cos_two_pi
    simp [hp1, hp2, hp3] at h5
    linarith
  have hc1 : -1 ≤ c := by
    nlinarith
  have hc2 : c ≤ 1 := by
    nlinarith
  apply abs_le.mpr
  constructor <;> linarith


theorem inequalities_232453 (a b c : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * cos x + b * cos (2 * x) + c * cos (3 * x))
  (h₁ : ∀ x, f x ≥ -1) :
  a + b + c ≤ 3 := by 
  have h1 := h₁ 0
  rw [h₀ 0] at h1
  have h1' : a + b + c ≥ -1 := by
    simp [Real.cos_zero] at h1
    linarith
  have h2 := h₁ (Real.pi)
  rw [h₀ (Real.pi)] at h2
  have hp1 : Real.cos (Real.pi) = -1 := Real.cos_pi
  have hp2 : Real.cos (2 * Real.pi) = 1 := by
    have h' : 2 * Real.pi = 2 * Real.pi := rfl
    rw [h']
    exact Real.cos_two_pi
  have hp3 : Real.cos (3 * Real.pi) = -1 := by
    have h' : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
    rw [h']
    have : Real.cos (Real.pi + 2 * Real.pi) = Real.cos Real.pi := by
      rw [Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
      norm_num
    rw [this, Real.cos_pi]
    all_goals norm_num
  have h2' : -a + b - c ≥ -1 := by
    simp [hp1, hp2, hp3] at h2
    linarith
  have h3 := h₁ (Real.pi / 2)
  rw [h₀ (Real.pi / 2)] at h3
  have hp1 : Real.cos (Real.pi / 2) = 0 := by
    exact Real.cos_pi_div_two
  have hp2 : Real.cos (2 * (Real.pi / 2)) = -1 := by
    have h' : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h']
    exact Real.cos_pi
  have hp3 : Real.cos (3 * (Real.pi / 2)) = 0 := by
    have h' : 3 * (Real.pi / 2) = Real.pi / 2 + Real.pi := by ring
    rw [h']
    have : Real.cos (Real.pi / 2 + Real.pi) = 0 := by
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
      norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
    linarith
  have h3' : b ≤ 1 := by
    simp [hp1, hp2, hp3] at h3
    linarith
  have h4 := h₁ (Real.pi / 3)
  rw [h₀ (Real.pi / 3)] at h4
  have hp1 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have hp2 : Real.cos (2 * (Real.pi / 3)) = -1 / 2 := by
    have h' : 2 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
    rw [h']
    rw [Real.cos_pi_sub]
    norm_num
  have hp3 : Real.cos (3 * (Real.pi / 3)) = -1 := by
    have h' : 3 * (Real.pi / 3) = Real.pi := by ring
    rw [h']
    exact Real.cos_pi
  have h4' : (a / 2) - (b / 2) - c ≥ -1 := by
    simp [hp1, hp2, hp3] at h4
    linarith
  have h5 := h₁ (2 * Real.pi / 3)
  rw [h₀ (2 * Real.pi / 3)] at h5
  have hp1 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have h' : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h']
    rw [Real.cos_pi_sub]
    norm_num
  have hp2 : Real.cos (2 * (2 * Real.pi / 3)) = -1 / 2 := by
    have h1 : 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 := by ring
    rw [h1]
    have hp21 : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
      have hp22 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by ring
      rw [hp22]
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
      norm_num [Real.cos_pi_div_three, Real.sin_pi_div_three]
    exact hp21
  have hp3 : Real.cos (3 * (2 * Real.pi / 3)) = 1 := by
    have h' : 3 * (2 * Real.pi / 3) = 2 * Real.pi := by ring
    rw [h']
    exact Real.cos_two_pi
  have h5' : - (a / 2) - (b / 2) + c ≥ -1 := by
    simp [hp1, hp2, hp3] at h5
    linarith
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            Real.sin_sq_add_cos_sq (Real.pi), Real.sin_sq_add_cos_sq (Real.pi / 2)]