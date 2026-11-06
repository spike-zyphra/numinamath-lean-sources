import Mathlib

theorem algebra_109540 :
    { (x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x + 1 / (y + 1 / z : ℚ) = 10 / 7 } = { (1, 2, 3) } := by
  ext ⟨x, y, z⟩
  simp
  constructor
  swap
  .
    rintro ⟨rfl, rfl, rfl⟩
    norm_num
  .
    rintro ⟨hx, hy, hz, h⟩
    have eq1 : (x : ℚ) + 1 / (y + (z : ℚ)⁻¹) = 10 / 7 := by
      norm_num at h ⊢
      exact_mod_cast h

    -- Convert equation to integer form.
    have eq6 : 7 * (x * (y * z + 1) + z) = 10 * (y * z + 1) := by
      have eq6a : (x : ℚ) + 1 / (y + (z : ℚ)⁻¹) = (10 / 7 : ℚ) := by
        linarith [h]
      have eq6b : (y + (z : ℚ)⁻¹) = (y * z + 1) / (z : ℚ) := by
        field_simp
        <;> ring
      rw [eq6b] at eq6a
      have eq6c : (x : ℚ) + (z / (y * z + 1 : ℚ)) = 10 / 7 := by 
        field_simp [(show (z : ℚ) ≠ 0 by positivity), (show (y * z + 1 : ℚ) ≠ 0 by
          have h1 : (y : ℚ) > 0 := by positivity
          have h2 : (z : ℚ) > 0 := by positivity
          have h3 : (y : ℚ) * (z : ℚ) > 0 := mul_pos h1 h2
          linarith
        )] at eq6a ⊢
        linarith
      have eq6d : (x : ℚ) * (y * z + 1) + (z : ℚ) = (10 / 7) * (y * z + 1) := by
        field_simp [(show (z : ℚ) ≠ 0 by positivity), (show (y * z + 1 : ℚ) ≠ 0 by
          have h1 : (y : ℚ) > 0 := by positivity
          have h2 : (z : ℚ) > 0 := by positivity
          have h3 : (y : ℚ) * (z : ℚ) > 0 := mul_pos h1 h2
          linarith
        )] at eq6c ⊢
        nlinarith
      have h₆_eq : (7 * (x * (y * z + 1) + z) = 10 * (y * z + 1) ) := by
        have h₆a : (x : ℚ) * (y * z + 1) + (z : ℚ) = (10 / 7) * (y * z + 1) := by
          linarith [eq6c]
        have h₆b : (7 * ((x : ℚ) * (y * z + 1) + (z : ℚ)) = 10 * (y * z + 1) ) := by 
          linarith
        exact_mod_cast h₆b
      exact_mod_cast h₆_eq

    have eq6 : 7 * (x * (y * z + 1) + z) = 10 * (y * z + 1) := by 
      have h₆_eq : (7 * (x * (y * z + 1) + z) = 10 * (y * z + 1) ) := by 
        norm_num at eq6 ⊢
        exact_mod_cast eq6
      linarith

    -- Now we need to show x=1
    have h₈ : x ≤ 1 := by 
      nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 2 : ℤ), sq_nonneg (z - 3 : ℤ), 
                  mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]

    have hx1 : x = 1 := by
      omega

    rw [show x = 1 by linarith [hx1]] at eq6

    have h₉ : y ≤ 3 := by 
      nlinarith [sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 2 : ℤ), sq_nonneg (z - 3 : ℤ), 
                  mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]

    have hy1 : y ≤ 3 := by linarith
    have hy2 : y > 0 := by linarith
    have : y = 1 ∨ y = 2 ∨ y = 3 := by
      omega
    rcases this with (h_eq | h_eq | h_eq)
    · -- y = 1
      rw [h_eq] at eq6
      exfalso
      have h_eq2 : z = 0 := by
        nlinarith
      omega
    · -- y = 2
      rw [h_eq] at eq6
      have h10 : z = 3 := by
        nlinarith
      have hx_eq : x = 1 := by linarith [hx1]
      have hy_eq : y = 2 := by linarith [h_eq]
      have hz_eq : z = 3 := by linarith [h10]
      simp [hx_eq, hy_eq, hz_eq]
    · -- y = 3
      rw [h_eq] at eq6
      exfalso
      have h11 : z = 0 := by
        nlinarith
      omega