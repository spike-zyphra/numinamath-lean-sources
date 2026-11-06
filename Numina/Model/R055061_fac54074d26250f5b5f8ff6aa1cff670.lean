import Mathlib

theorem algebra_295541 {x : ℚ} (hx : x > 0) (h : √x + √(x + 13) = √(4 * x + 17)) :
    ∃ a b : ℕ, a.gcd b = 1 ∧ x = a / b ∧ a + b = 13 := by
  have h₁ : √x + √(x + 13) = √(4 * x + 17) := h
  have h2 : √x ≥ 0 := by positivity
  have h3 : √(x + 13) ≥ 0 := by positivity
  have h4 : √(4 * x + 17) ≥ 0 := by positivity
  have h5 : (√x + √(x + 13)) ^ 2 = (√(4 * x + 17)) ^ 2 := by
    rw [h₁]
  have h6 : (√x + √(x + 13)) ^ 2 = (√x) ^ 2 + (√(x + 13)) ^ 2 + 2 * (√x * √(x + 13)) := by ring
  have h7 : (√(4 * x + 17)) ^ 2 = 4 * x + 17 := by
    have h8 : (4 * x + 17) ≥ 0 := by
      have hx1 : x > 0 := hx
      have hx2 : 4 * x > 0 := by linarith
      linarith
    exact Real.sq_sqrt (by exact_mod_cast h8)
  have h9 : (√x) ^ 2 = x := by
    have hx1 : x ≥ 0 := by linarith
    exact Real.sq_sqrt (by exact_mod_cast hx1)
  have h10 : (√(x + 13)) ^ 2 = x + 13 := by
    have hx1 : x + 13 ≥ 0 := by
      linarith
    exact Real.sq_sqrt (by exact_mod_cast hx1)
  rw [h6] at h5
  rw [h9, h10] at h5
  rw [h7] at h5
  have h11 : 2 * (√x * √(x + 13)) = 2 * x + 4 := by linarith
  have h12 : √x * √(x + 13) = x + 2 := by
    nlinarith
  have h13 : √x * √(x + 13) = √(x * (x + 13)) := by
    have hx1 : x ≥ 0 := by linarith
    have hx2 : x + 13 ≥ 0 := by linarith
    have h14 : √x * √(x + 13) = √(x * (x + 13)) := by
      rw [← Real.sqrt_mul (by positivity)]
      all_goals positivity
    exact h14
  rw [h13] at h12
  have h14 : √(x * (x + 13)) ^ 2 = (x + 2) ^ 2 := by
    rw [h12]
  have h15 : √(x * (x + 13)) ^ 2 = x * (x + 13) := by
    have h16 : x * (x + 13) ≥ 0 := by
      nlinarith
    exact Real.sq_sqrt (by exact_mod_cast h16)
  rw [h15] at h14
  have h17 : x * (x + 13) = (x + 2) ^ 2 := by
    exact_mod_cast h14
  have h18 : x ^ 2 + 13 * x = x ^ 2 + 4 * x + 4 := by
    have h19 : x * (x + 13) = (x + 2) ^ 2 := h17
    have h20 : x * (x + 13) = x^2 + 13 * x := by
      ring
    have h21 : (x + 2) ^ 2 = x^2 + 4 * x + 4 := by
      ring
    rw [h20, h21] at h19
    linarith
  have h19 : 9 * x = 4 := by
    linarith
  have hx_eq : x = 4 / 9 := by
    linarith
  use 4, 9
  constructor
  · norm_num [Nat.gcd]
  constructor
  · exact_mod_cast hx_eq
  · norm_num