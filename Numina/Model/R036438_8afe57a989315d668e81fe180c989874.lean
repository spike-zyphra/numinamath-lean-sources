import Mathlib

open Real

theorem algebra_12411 {g : ℝ → ℝ}
    (hg : ∀ x, x ≤ 0 → g x = -x)
    (hg' : ∀ x, x > 0 → g x = 2 * x - 41)
    (a : ℝ) (ha : a < 0) :
    g (g (g 10.5)) = g (g (g a)) ↔ a = -30.5 := by
  constructor
  · -- Assume g (g (g 10.5)) = g (g (g a)), prove a = -30.5
    intro h_eq
    have h1 : g 10.5 = -20 := by
      specialize hg' 10.5 (by norm_num)
      rw [hg']
      norm_num
    have h2 : g (g 10.5) = 20 := by 
      rw [h1]
      specialize hg (-20) (by norm_num)
      rw [hg]
      norm_num
    have h3 : g (g (g 10.5)) = -1 := by 
      rw [h2]
      specialize hg' 20 (by norm_num)
      rw [hg']
      norm_num
    have ha1 : g a = -a := by
      apply hg
      linarith
    have ha2 : g (g a) = -2 * a - 41 := by 
      rw [ha1]
      have h4 : -a > 0 := by linarith
      specialize hg' (-a) h4
      rw [hg']
      ring
    by_cases h5 : -2 * a - 41 ≤ 0
    · -- Case where -2 * a - 41 ≤ 0
      have ha3 : g (g (g a)) = 2 * a + 41 := by 
        rw [ha2]
        specialize hg (-2 * a - 41) h5
        rw [hg]
        all_goals linarith
      rw [h3] at h_eq
      rw [ha3] at h_eq
      nlinarith [h_eq, h5]
    · -- Case where -2 * a - 41 > 0
      have h6 : -2 * a - 41 > 0 := by 
        linarith 
      have ha3 : g (g (g a)) = -4 * a - 123 := by 
        rw [ha2]
        specialize hg' (-2 * a - 41) h6
        rw [hg']
        ring 
      rw [h3] at h_eq
      rw [ha3] at h_eq 
      nlinarith [h_eq, h6]
  · -- Assume a = -30.5, prove g (g (g 10.5)) = g (g (g a))
    intro h_eq
    have ha_eq : a = -30.5 := by
      linarith 
    have h1 : g 10.5 = -20 := by 
      specialize hg' 10.5 (by norm_num)
      rw [hg']
      norm_num 
    have h2 : g (g 10.5) = 20 := by 
      rw [h1]
      specialize hg (-20) (by norm_num)
      rw [hg]
      norm_num
    have h3 : g (g (g 10.5)) = -1 := by 
      rw [h2]
      specialize hg' 20 (by norm_num)
      rw [hg']
      norm_num 
    have ha1 : g a = 30.5 := by 
      rw [ha_eq]
      specialize hg (-30.5) (by norm_num)
      rw [hg]
      norm_num 
    have ha2 : g (g a) = 20 := by 
      rw [ha1]
      specialize hg' 30.5 (by norm_num)
      rw [hg']
      norm_num 
    have ha3 : g (g (g a)) = -1 := by
      rw [ha2]
      specialize hg' 20 (by norm_num)
      rw [hg']
      norm_num
    rw [h3, ha3]