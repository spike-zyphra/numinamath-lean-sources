import Mathlib

theorem algebra_311018 :
    IsGreatest {x * y + 2 * x * z | (x : ℝ) (y : ℝ) (z : ℝ) (_ : x > 0) (_ : y > 0) (_ : z > 0) (_ : √(x ^ 2 + y ^ 2) + z = 1) } (√3 / 3) := by
  constructor
  . use √3 / 3, 1 / 3, 1 / 3
    ring_nf
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp
    norm_num
  . rintro w ⟨x, y, z, hx, hy, hz, h, rfl⟩
    replace h : √(x ^ 2 + y ^ 2) = 1 - z := by linarith only [h]
    have h₁ : x ^ 2 = (1 - z - y) * (1 - z + y) := by
      apply_fun (· ^ 2) at h
      simp [show x ^ 2 + y ^ 2 ≥ 0 by positivity] at h
      linarith only [h]
    have h₂ : 1 - z + y > 0 := by
      rw [← h]
      positivity
    have h₃ : 1 - z - y > 0 := by
      have h₃ : x ^ 2 > 0 := by positivity
      rw [h₁] at h₃
      exact (pos_iff_pos_of_mul_pos h₃).mpr h₂
    have h₄ := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin 3)) ![1, 1, 2] ![3 * (1 - z - y), 1 - z + y, y + 2 * z]
    simp at h₄
    specialize h₄ ?_ ?_ ?_
    {
      intro i
      fin_cases i <;> simp
    }
    {
      norm_num [Finset.sum]
    }
    {
      intro i
      fin_cases i
      all_goals
        simp [-sub_nonneg]
        positivity
    }
    simp [Finset.sum, Finset.prod] at h₄
    conv_rhs at h₄ => ring_nf
    rw [Real.rpow_le_one_iff_of_pos (by positivity)] at h₄
    norm_num at h₄
    rw [← sq_le_sq₀ (by positivity) (by positivity)]
    calc (x * y + 2 * x * z) ^ 2
      _ = x ^ 2 * (y + 2 * z) ^ 2 := by ring
      _ = (1 - z - y) * (1 - z + y) * (y + 2 * z) ^ 2 := by rw [h₁]
      _ ≤ 1 / 3 := by linarith only [h₄]
      _ = (√3 / 3) ^ 2 := by ring_nf; norm_num
