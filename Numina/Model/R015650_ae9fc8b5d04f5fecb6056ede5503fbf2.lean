import Mathlib

theorem algebra_1704 (v₀ v₁ v₂ : ℝ) (h : 0 < v₀ ∧ 0 < v₁ ∧ 0 < v₂)
    (h1 : 400 / v₀ + 300 / v₁ + (800 - 700) / v₂ = 400 / v₁ + 300 / v₂ + (800 - 700) / v₀)
    (h2 : v₁ / v₀ = 3 / 4) (h3 : v₂ / v₁ = 5 / 4): v₀ / v₂ = 33 / 29 := by 
  rcases h with ⟨hv₀, hv₁, hv₂⟩
  have eq3 : v₁ = 3 / 4 * v₀ := by
    have h4 : v₀ ≠ 0 := by linarith
    field_simp [h4] at h2 ⊢
    linarith
  have eq4 : v₂ = 5 / 4 * v₁ := by
    have h4 : v₁ ≠ 0 := by linarith
    field_simp [h4] at h3 ⊢
    linarith
  have eq5 : v₂ = 15 / 16 * v₀ := by 
    rw [eq3] at eq4 
    linarith 
  have eq1' : 400 / v₀ + 300 / v₁ + 100 / v₂ = 400 / v₁ + 300 / v₂ + 100 / v₀ := by
    have h_eq1 : 400 / v₀ + 300 / v₁ + (800 - 700) / v₂ = 400 / v₁ + 300 / v₂ + (800 - 700) / v₀ := h1
    norm_num at h_eq1 ⊢
    all_goals linarith 
  have eq6 : 300 / v₀ - 100 / v₁ - 200 / v₂ = 0 := by 
    have eq1'' : 400 / v₀ + 300 / v₁ + 100 / v₂ = 400 / v₁ + 300 / v₂ + 100 / v₀ := eq1'
    have eq7 : 400 / v₀ + 300 / v₁ + 100 / v₂ - (400 / v₁ + 300 / v₂ + 100 / v₀) = 0 := by 
      linarith [eq1'']
    have eq8 : 400 / v₀ + 300 / v₁ + 100 / v₂ - (400 / v₁ + 300 / v₂ + 100 / v₀) = 300 / v₀ - 100 / v₁ - 200 / v₂ := by 
      field_simp [show v₀ ≠ 0 by linarith, show v₁ ≠ 0 by linarith, 
                   show v₂ ≠ 0 by linarith]
      <;> ring
    linarith [eq7, eq8]
  have eq7 : 300 / v₀ - 100 / v₁ - 200 / v₂ = 0 := eq6 
  have h4 : (300 - 100 / (3/4) - 200 / (15/16)) = 0 := by 
    have h5 : v₀ ≠ 0 := by linarith 
    have h6 : v₁ = 3/4 * v₀ := eq3
    have h7 : v₂ = 15/16 * v₀ := eq5 
    have eq8 : 300 / v₀ - 100 / v₁ - 200 / v₂ = (300 - 100 / (3/4) - 200 / (15/16)) / v₀ := by 
      rw [show v₁ = 3/4 * v₀ by linarith [eq3]] 
      rw [show v₂ = 15/16 * v₀ by linarith [eq5]] 
      field_simp [h5, show v₀ ≠ 0 by linarith] 
      <;> ring
    have eq9 : (300 - 100 / (3/4) - 200 / (15/16)) / v₀ = 0 := by
      rw [eq8] at eq7 
      linarith 
    have h8 : v₀ ≠ 0 := h5 
    field_simp [h8] at eq9 ⊢ 
    <;> nlinarith 
  norm_num at h4 
  all_goals 
    linarith