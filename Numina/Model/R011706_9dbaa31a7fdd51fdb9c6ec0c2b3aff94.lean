import Mathlib

theorem calculus_41041 (a b c : ℝ) (f : ℝ × ℝ × ℝ → ℝ)
    (hf : f = fun ⟨x, y, z⟩ => a * x + b * y + c * z)
    (h1 : f (3, 1, 1) > f (2, 1, 1))
    (h2 : f (2, 2, 3) > f (2, 3, 4))
    (h3 : f (3, 3, 4) > f (3, 3, 3))
    (x y z : ℝ) (hx : x ∈ Set.Icc (-5) 5) (hy : y ∈ Set.Icc (-5) 5) (hz : z ∈ Set.Icc (-5) 5) (H : IsMaxOn f {(x, y, z) : ℝ × ℝ × ℝ | x ∈ Set.Icc (-5) 5 ∧ y ∈ Set.Icc (-5) 5 ∧ z ∈ Set.Icc (-5) 5} (x, y, z)) :
    (x, y, z) = (5, -5, 5) := by

  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩

  have h1' : a > 0 := by
    simp [hf] at h1
    linarith
  
  have h2' : b < -c := by
    simp [hf] at h2
    linarith
  
  have h3' : c > 0 := by
    simp [hf] at h3
    linarith
  
  -- Show that f(5, -5, 5) is the maximum value.
  have h4 : f (5, -5, 5) ≤ f (x, y, z) := by 
    have h5 : (5, -5, 5) ∈ {(x, y, z) : ℝ × ℝ × ℝ | x ∈ Set.Icc (-5) 5 ∧ y ∈ Set.Icc (-5) 5 ∧ z ∈ Set.Icc (-5) 5} := by 
      simp only [Set.mem_setOf_eq]
      constructor
      · -- Show that 5 ∈ Icc (-5) 5
        norm_num [Set.mem_Icc]
      constructor
      · -- Show that -5 ∈ Icc (-5) 5
        norm_num [Set.mem_Icc]
      · -- Show that 5 ∈ Icc (-5) 5
        norm_num [Set.mem_Icc]
    have h6 : f (5, -5, 5) ≤ f (x, y, z) := by 
      apply H
      exact h5
    linarith

  have h5 : f (5, -5, 5) ≥ f (x, y, z) := by
    simp [hf]
    -- f(5, -5, 5) = 5a -5b + 5c, f(x,y,z) = ax +by +cz
    -- 5a -5b +5c ≥ ax +by +cz 
    nlinarith [show a > 0 by linarith, show c > 0 by linarith, 
      show b < 0 by nlinarith, hx1, hx2, hy1, hy2, hz1, hz2]

  have h8 : f (x, y, z) = f (5, -5, 5) := by linarith
  simp [hf] at h8

  have hx_eq : x - 5 = 0 := by
    nlinarith [show a > 0 by linarith, show c > 0 by linarith, show b < 0 by nlinarith, 
      hx1, hx2, hy1, hy2, hz1, hz2]

  have hy_eq : y + 5 = 0 := by
    nlinarith [show a > 0 by linarith, show c > 0 by linarith, show b < 0 by nlinarith, 
      hx1, hx2, hy1, hy2, hz1, hz2]

  have hz_eq : z - 5 = 0 := by 
    nlinarith [show a > 0 by linarith, show c > 0 by linarith, show b < 0 by nlinarith, 
      hx1, hx2, hy1, hy2, hz1, hz2]

  have hx5 : x = 5 := by linarith
  have hy5 : y = -5 := by linarith
  have hz5 : z = 5 := by linarith

  simp [hx5, hy5, hz5]