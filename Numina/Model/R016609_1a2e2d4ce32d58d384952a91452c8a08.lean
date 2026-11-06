import Mathlib

theorem calculus_60163 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => a * x + b + 9 / x) :
    ∃ x₀ ∈ Set.Icc 1 9, |f x₀| ≥ 2 := by 
  by_contra h
  push_neg at h
  have h1 : ∀ x₀ ∈ Set.Icc 1 9, |f x₀| < 2 := h
  have h11 := h1 1 (Set.left_mem_Icc.mpr (by norm_num))
  have h99 := h1 9 (Set.right_mem_Icc.mpr (by norm_num))
  have h33 := h1 3 (by norm_num [Set.mem_Icc])
  have h12 : -2 < a + b + 9 := by
    have h11' : |f 1| < 2 := h11
    rw [hf] at h11'
    simp at h11'
    linarith [abs_lt.mp h11']
  have h13 : a + b + 9 < 2 := by
    have h11' : |f 1| < 2 := h11
    rw [hf] at h11'
    simp at h11'
    linarith [abs_lt.mp h11']
  have h31 : -2 < a * 3 + b + 9 / (3 : ℝ) := by
    have h33' : |f 3| < 2 := h33
    rw [hf] at h33'
    simp at h33'
    linarith [abs_lt.mp h33']
  have h32 : a * 3 + b + 9 / (3 : ℝ) < 2 := by
    have h33' : |f 3| < 2 := h33
    rw [hf] at h33'
    simp at h33'
    linarith [abs_lt.mp h33']
  have h91 : -2 < a * 9 + b + 9 / (9 : ℝ) := by
    have h99' : |f 9| < 2 := h99
    rw [hf] at h99'
    simp at h99'
    linarith [abs_lt.mp h99']
  have h92 : a * 9 + b + 9 / (9 : ℝ) < 2 := by
    have h99' : |f 9| < 2 := h99
    rw [hf] at h99'
    simp at h99'
    linarith [abs_lt.mp h99']
  have h14 : -11 < a + b := by
    linarith
  have h15 : a + b < -7 := by
    linarith
  have h33' : -5 < 3 * a + b := by
    norm_num at h31 h32
    linarith
  have h34 : 3 * a + b < -1 := by
    norm_num at h31 h32
    linarith
  have h93 : -3 < 9 * a + b := by
    norm_num at h91 h92
    linarith
  have h94 : 9 * a + b < 1 := by
    norm_num at h91 h92
    linarith
  linarith