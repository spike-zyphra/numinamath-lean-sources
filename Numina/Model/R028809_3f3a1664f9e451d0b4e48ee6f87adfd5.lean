import Mathlib

theorem algebra_277617 {p p1 p2 d1 : ℝ} (hp : p > 0) (hp1 : p1 > 0) (hp2 : p2 > 0)
    (hd1 : d1 > 0) (h_p1_lt_p : p1 < p) (h_p2_lt_p : p2 < p) :
    {(x, d) : ℝ × ℝ | x > 0 ∧ d > 0 ∧ p - p1 = d1 * (p / d) ∧ p - p2 = x * (p / d)} =
    {(d1 * (p - p2) / (p - p1), d1 * p / (p - p1))} := by
  ext ⟨x, d⟩ 
  constructor
  · -- Assume (x, d) is in the left side 
    rintro ⟨hx, hd, h1, h2⟩ 
    have h3 : p - p1 > 0 := by linarith 
    have h4 : p - p2 > 0 := by linarith 
    have h5 : d ≠ 0 := by linarith 
    have eq1 : (p - p1) * d = d1 * p := by 
      have hne3 : d ≠ 0 := by nlinarith
      field_simp [hne3] at h1 ⊢ 
      nlinarith 
    have eq2 : (p - p2) * d = x * p := by 
      have hne3 : d ≠ 0 := by nlinarith 
      field_simp [hne3] at h2 ⊢ 
      nlinarith 
    have eq3 : d = d1 * p / (p - p1) := by 
      have hne1 : p - p1 ≠ 0 := by linarith 
      have hne2 : p ≠ 0 := by linarith 
      field_simp [hne1, hne2] at eq1 ⊢ 
      <;> nlinarith 
    have eq4 : x = d1 * (p - p2) / (p - p1) := by 
      rw [eq3] at eq2 
      have hne1 : p - p1 ≠ 0 := by linarith 
      have hne2 : p ≠ 0 := by linarith 
      field_simp [hne1, hne2] at eq2 ⊢ 
      <;> nlinarith 
    simp [eq4, eq3] 
  · -- Assume (x, d) is in the right side 
    rintro ⟨rfl, rfl⟩ 
    have h3 : p - p1 > 0 := by linarith 
    have h4 : p - p2 > 0 := by linarith 
    constructor 
    · -- show x>0 
      have h5 : p - p1 > 0 := by linarith 
      have h3 : p - p2 > 0 := by linarith 
      have h6 : d1 > 0 := hd1 
      have h7 : p > 0 := hp 
      have h8 : (d1 * (p - p2) / (p - p1)) > 0 := by 
        apply div_pos 
        nlinarith 
        nlinarith 
      exact_mod_cast h8 
    constructor 
    · -- show d>0 
      have h5 : p - p1 > 0 := by linarith 
      have h6 : d1 > 0 := hd1 
      have h7 : p > 0 := hp 
      have h8 : (d1 * p / (p - p1)) > 0 := by 
        apply div_pos 
        nlinarith 
        nlinarith 
      exact_mod_cast h8 
    constructor 
    · -- show 3 
      field_simp [(show p - p1 ≠ 0 by linarith), (show p ≠ 0 by linarith)]
      <;> ring 
    · -- show 4 
      field_simp [(show p - p1 ≠ 0 by linarith), (show p ≠ 0 by linarith)]
      <;> ring