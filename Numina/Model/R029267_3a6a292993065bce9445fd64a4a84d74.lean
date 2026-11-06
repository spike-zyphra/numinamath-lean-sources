import Mathlib

open Real Set

theorem algebra_6154 (a : ℝ) : (∃ x y : ℝ, x ≠ y ∧ |x| + 5 * a = a * x - 1 ∧
    |y| + 5 * a = a * y - 1) ↔ a ∈ Ioo (-1) (-1 / 5) := by
  constructor
  · -- Forward direction
    rintro ⟨x, y, hxy, hx, hy⟩
    by_cases h1 : x ≥ 0
    · -- x ≥ 0
      have hx_eq : x * (1 - a) = -1 - 5 * a := by
        rw [abs_of_nonneg h1] at hx
        linarith
      by_cases h2 : y ≥ 0
      · -- y ≥ 0
        have hy_eq : y * (1 - a) = -1 - 5 * a := by
          rw [abs_of_nonneg h2] at hy
          linarith
        have h1a : (x - y) * (1 - a) = 0 := by
          linarith [hx_eq, hy_eq]
        cases' (mul_eq_zero.mp h1a) with h2a h3a
        · -- x - y = 0
          exfalso 
          apply hxy 
          linarith
        · -- 1 - a = 0
          have ha1 : a = 1 := by linarith
          rw [ha1] at hx_eq 
          nlinarith
      · -- y < 0
        have hy_eq : y * (1 + a) = 1 + 5 * a := by 
          rw [abs_of_neg (show y < 0 by
            by_contra h
            push_neg at h 
            have : y ≥ 0 := by linarith
            contradiction
          )] at hy 
          linarith
        by_cases h4a : a > -1
        · -- Now prove that with a > -1 and both equations.
          have h6 : -1 < a := by linarith
          have h6a : a < -1 / 5 := by
            nlinarith [abs_nonneg x, abs_nonneg y
            ]
          exact  ⟨h6, h6a⟩
        · -- Assume for contradiction that a ≤ -1
          have ha2 : a ≤ -1 := by
            by_contra h2a 
            nlinarith
          nlinarith [abs_nonneg x, abs_nonneg y
          ]
    · -- x < 0
      have hx_eq : x * (1 + a) = 1 + 5 * a := by 
        rw [abs_of_neg (show x < 0 by
          by_contra h
          push_neg at h
          have : x ≥ 0 := by linarith
          contradiction 
        )] at hx 
        linarith 
      by_cases h2 : y ≥ 0 
      · -- y ≥ 0
        have hy_eq : y * (1 - a) = -1 - 5 * a := by 
          rw [abs_of_nonneg h2] at hy 
          linarith
        by_cases h4a : a > -1
        · -- Now prove that with a > -1 and both equations.
          have h6 : -1 < a := by linarith
          have h6a : a < -1 / 5 := by 
            nlinarith [abs_nonneg x, abs_nonneg y
            ]
          exact  ⟨h6, h6a⟩
        · -- Assume for contradiction that a ≤ -1
          have ha2 : a ≤ -1 := by 
            by_contra h2a
            nlinarith
          nlinarith [abs_nonneg x, abs_nonneg y
          ]
      · -- y < 0
        have hy_eq : y * (1 + a) = 1 + 5 * a := by 
          rw [abs_of_neg (show y < 0 by
            by_contra h
            push_neg at h
            have : y ≥ 0 := by linarith
            contradiction
          )] at hy
          linarith
        have h1a : (x - y) * (1 + a) = 0 := by
          linarith [hx_eq, hy_eq]
        cases' (mul_eq_zero.mp h1a) with h2a h3a
        · -- x - y = 0 
          exfalso
          apply hxy
          linarith
        · -- 1 + a = 0
          have ha1 : a = -1 := by linarith
          rw [ha1] at hx_eq
          nlinarith
  · -- Backward direction: if a ∈ (-1, -1/5), then there's two distinct roots.
    rintro ⟨ha1, ha2⟩
    use ((-1 - 5 * a) / (1 - a)), ((1 + 5 * a) / (1 + a))
    constructor 
    · -- Show that x ≠ y 
      by_contra h_eq 
      field_simp [(show 1 - a ≠ 0 by nlinarith), (show 1 + a ≠ 0 by nlinarith)] at h_eq ⊢
      nlinarith
    constructor 
    · -- Show |x| + 5 * a = a * x - 1
      have h4 : (-1 - 5 * a) / (1 - a) ≥ 0 := by
        apply div_nonneg 
        · -- Show -1 - 5 * a ≥ 0 
          nlinarith 
        · -- Show 1 - a ≥ 0 
          nlinarith 
      rw [abs_of_nonneg h4] 
      field_simp [(show 1 - a ≠ 0 by nlinarith)]
      <;> linarith
    · -- Show |y| + 5 * a = a * y - 1 
      have h5 : (1 + 5 * a) / (1 + a) < 0 := by 
        apply div_neg_of_neg_of_pos 
        · -- Show 1 + 5 * a < 0 
          nlinarith 
        · -- Show 1 + a > 0 
          nlinarith 
      rw [abs_of_neg h5]
      field_simp [(show 1 + a ≠ 0 by nlinarith)]
      <;> linarith