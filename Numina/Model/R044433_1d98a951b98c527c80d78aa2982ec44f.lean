import Mathlib

theorem algebra_144206 (xiao_zhao xiao_qian xiao_sun t t_sun : ℝ)
    (h : xiao_zhao > 0 ∧ xiao_qian > 0 ∧ xiao_sun > 0)
    (h1 : xiao_zhao / xiao_qian = 3 / 2)
    (h2 : (xiao_zhao + xiao_qian) * t = 2000)
    (h3 : (xiao_zhao + xiao_sun) * (t + 5/4) = 2000)
    (h4 : (xiao_zhao + xiao_qian) * (t + 5) = 4000) 
    (h5 : t_sun = 2000 / xiao_sun):
    t_sun = 25 := by
  rcases h with ⟨hz, hq, hs⟩
  have h6 : xiao_zhao = 3 / 2 * xiao_qian := by
    have hq' : xiao_qian > 0 := hq
    field_simp [hq'] at h1
    linarith
  have h7 : xiao_zhao + xiao_qian = 400 := by
    nlinarith
  have h8 : xiao_qian = 160 := by
    nlinarith
  have h9 : xiao_zhao = 240 := by
    rw [h8] at h6
    linarith
  have h10 : t = 5 := by
    nlinarith
  have h11 : xiao_sun = 80 := by
    rw [h10, h9] at h3
    nlinarith
  have hx12 : t_sun = 25 := by
    have h12 : xiao_sun = 80 := h11
    have h13 : t_sun = 2000 / xiao_sun := by linarith [h5]
    rw [h12] at h13
    have h15 : t_sun = 25 := by
      norm_num at h13 ⊢
      linarith 
    linarith
  linarith [hx12]