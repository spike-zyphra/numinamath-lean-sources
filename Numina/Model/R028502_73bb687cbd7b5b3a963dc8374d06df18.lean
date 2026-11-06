import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_144704
  (A B C : EuclideanSpace ℝ (Fin 2))
  (a b c : ℝ)
  (ha : a = dist B C)
  (hb : b = dist A C)
  (hc : c = dist A B)
  (h : a + b + c = 2) :
  1 ≤ a * b + b * c + c * a - a * b * c ∧
  a * b + b * c + c * a - a * b * c ≤ 1 + 1 / 27 := by
  have h1 : a ≥ 0 := by 
    rw [ha]
    apply dist_nonneg
  have h2 : b ≥ 0 := by 
    rw [hb]
    apply dist_nonneg
  have h3 : c ≥ 0 := by 
    rw [hc]
    apply dist_nonneg
  have h10 : a ≤ b + c := by 
    rw [ha, hb, hc]
    have h4 : dist B C ≤ dist A C + dist A B := by 
      have h5 : dist B C ≤ dist B A + dist A C := by 
        apply dist_triangle
      have h2 : dist B A = dist A B := by 
        apply dist_comm
      rw [h2] at h5 
      all_goals linarith
    linarith
  have h20 : b ≤ a + c := by 
    rw [ha, hb, hc]
    have h5 : dist A C ≤ dist B C + dist A B := by 
      have h6 : dist A C ≤ dist A B + dist B C := by 
        have h1 : dist A C ≤ dist A B + dist B C := by 
          apply dist_triangle 
        linarith 
      linarith 
    linarith
  have h30 : c ≤ a + b := by 
    rw [ha, hb, hc]
    have h7 : dist A B ≤ dist B C + dist A C := by 
      have h1 : dist A B ≤ dist A C + dist C B := by 
        apply dist_triangle
      have h2 : dist C B = dist B C := by 
        apply dist_comm 
      rw [h2] at h1 
      linarith 
    linarith
  constructor 
  · -- Prove 1 ≤ a * b + b * c + c * a - a * b * c 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      h, mul_nonneg h1 h2, mul_nonneg h2 h3, mul_nonneg h1 h3, 
        mul_nonneg h1 (show (0 : ℝ) ≤ b + c by linarith), 
          mul_nonneg h2 (show (0 : ℝ) ≤ a + c by linarith), 
            mul_nonneg h3 (show (0 : ℝ) ≤ a + b by linarith), 
              mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr h20), 
                mul_nonneg (sub_nonneg.mpr h20) (sub_nonneg.mpr h30), 
                  mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr h30)
                  ]
  · -- Prove a * b + b * c + c * a - a * b * c ≤ 1 + 1 / 27 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
      h, mul_nonneg h1 h2, mul_nonneg h2 h3, mul_nonneg h1 h3, 
        mul_nonneg h1 (show (0 : ℝ) ≤ b + c by linarith), 
          mul_nonneg h2 (show (0 : ℝ) ≤ a + c by linarith), 
            mul_nonneg h3 (show (0 : ℝ) ≤ a + b by linarith), 
              mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr h20), 
                mul_nonneg (sub_nonneg.mpr h20) (sub_nonneg.mpr h30), 
                  mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr h30)
                  ]