import Mathlib

theorem algebra_296955 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (f : ℝ → ℝ) (hf : f = fun x => a ^ x)
    (h : f ⁻¹' {x | x = Real.sqrt 2 / 2} = {-1 / 4}) : a = 4 := by
  have h1 : -1 / 4 ∈ f ⁻¹' {x | x = Real.sqrt 2 / 2} := by
    rw [h]
    simp
  rw [hf] at h1
  simp at h1
  have h2 : a ^ (-1 / 4 : ℝ) = Real.sqrt 2 / 2 := by
    linarith
  have h3 : a = 4 := by
    have h4 : a ^ (-1 / 4 : ℝ) = Real.sqrt 2 / 2 := h2
    have h5 : a = ((Real.sqrt 2 / 2) ^ (-4 : ℝ)) := by
      have h7 : a = ((a ^ (-1 / 4 : ℝ)) ) ^ (-4 : ℝ) := by
        calc
          a = (a ^ (-1 / 4 : ℝ) ) ^ (-4 : ℝ) := by
            rw [← Real.rpow_mul]
            norm_num
            all_goals linarith [ha.1]
          _ = ((a ^ (-1 / 4 : ℝ)) ) ^ (-4 : ℝ) := by rfl
      rw [h4] at h7
      linarith
    have h6 : (Real.sqrt 2 / 2 : ℝ) ^ (-4 : ℝ) = (4 : ℝ) := by
      have h7 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      have h8 : (Real.sqrt 2 / 2 : ℝ) = (2 : ℝ) ^ (-1 / 2 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) = Real.sqrt 2 / (2 : ℝ) := by norm_num
          _ = ( (2 : ℝ) ^ (1 / 2 : ℝ) ) / (2 : ℝ) := by
            rw [h7]
          _ = (2 : ℝ) ^ (1 / 2 : ℝ) * ( (2 : ℝ ) ) ^ (-1 : ℝ ) := by
            field_simp [Real.rpow_mul]
            all_goals linarith
          _ = (2 : ℝ ) ^ ((1 / 2 : ℝ ) + (-1 : ℝ ) ) := by
            rw [← Real.rpow_add]
            ring_nf
            all_goals linarith
          _ = (2 : ℝ ) ^ (-1 / 2 : ℝ ) := by
            ring_nf
            all_goals norm_num
      rw [h8]
      have h9 : ((2 : ℝ) ^ (-1 / 2 : ℝ) ) ^ (-4 : ℝ) = (2 : ℝ ) ^ (2 : ℝ ) := by
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h9]
      norm_num
    rw [h6] at h5
    linarith
  exact h3