import Mathlib

open Real

theorem inequalities_246305 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    64 ≤ (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) ∧
    (64 = (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) ↔ x = y ∧ y = z) := by
  constructor
  · -- Prove the inequality
    have h1 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) = (x + 1) * (y + 1) * (z + 1) / (x * y * z) := by
      field_simp
      all_goals ring
    rw [h2]
    have h4 : (x + 1) * (y + 1) * (z + 1) ≥ 64 * (x * y * z) := by
      have h8 : (x + 1) * (y + 1) * (z + 1) - 64 * (x * y * z) ≥ 0 := by
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          hsum, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith)]
      linarith
    have h64 : (x + 1) * (y + 1) * (z + 1) / (x * y * z) ≥ 64 := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith only [h4, show 0 < x * y * z by positivity]
    linarith only [h64, show 0 < x * y * z by positivity]
  · -- Prove the equality holds
    constructor
    · -- Assume 64 = product, prove x = y ∧ y = z
      intro ht
      have h1 : 0 < x * y * z := by
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h3 : (x + 1) * (y + 1) * (z + 1) = 64 * (x * y * z) := by
        have h10 : (x + 1) * (y + 1) * (z + 1) / (x * y * z) = 64 := by
          have h_eq : (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) = (x + 1) * (y + 1) * (z + 1) / (x * y * z) := by
            field_simp
            all_goals ring
          rw [h_eq] at ht
          have h2 : (x + 1) * (y + 1) * (z + 1) / (x * y * z) = 64 := by linarith
          linarith
        have h30 : (x + 1) * (y + 1) * (z + 1) = 64 * (x * y * z) := by
          have h40 : 0 < x * y * z := h1
          field_simp at h10 ⊢
          nlinarith [show 0 < x * y * z by positivity]
        linarith
      have h10 : x = y := by
        have h70 : (x - y) ^ 2 = 0 := by
          nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              hsum, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
              mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith)]
        have h80 : x - y = 0 := by nlinarith
        linarith
      have h11 : y = z := by
        have h20 : (y - z) ^ 2 = 0 := by
          rw [show x = y by linarith [h10]] at h3 hsum
          nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
                  sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                  hsum, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
                  mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith)]
        have h30 : y - z = 0 := by nlinarith
        linarith
      constructor
      · exact h10
      · exact h11
    · -- Assume x=y ∧ y=z, prove 64 = product
      rintro ⟨h1, h2⟩
      have h3 : z = x := by linarith [show y = x by linarith [h1]]
      have h9 : x = 1 / 3 := by
        have eq1 : x + y + z = 1 := hsum
        rw [show y = x by linarith [h1], show z = x by linarith [h3]] at eq1
        nlinarith
      have heq : (1 + 1 / x) * (1 + 1 / y) * (1 + 1 / z) = 64 := by
        rw [show y = x by linarith [h1], show z = x by linarith [h3]]
        rw [h9]
        norm_num
      linarith