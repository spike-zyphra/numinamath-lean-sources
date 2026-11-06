import Mathlib

theorem algebra_247876 : {(a, b) : ℝ × ℝ |
    ∃ x, x^2 + a * x + b^2 = 0 ∧ x^2 + b * x + a^2 = 0} = {(0, 0)} := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Suppose there is a common root
    rintro ⟨x, h₁, h₂⟩
    have h3 : (b - a) * x + (a^2 - b^2) = 0 := by
      nlinarith
    have h4 : (b - a) * (x - (a + b)) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- If b = a, then both quadratics become x^2 + a*x + a^2 = 0
      have h7 : b = a := by linarith
      have h8 : x^2 + a * x + a^2 = 0 := by
        rw [show b = a by linarith [h7]] at h₁
        linarith
      have h10 : a^2 ≤ 0 := by
        nlinarith [sq_nonneg (x + a / 2)]
      have h11 : a = 0 := by nlinarith [sq_nonneg a]
      have h12 : b = 0 := by
        rw [show b = a by linarith [h7]]
        linarith [h11]
      simp [h11, h12]
    · -- If x = a + b
      have h7 : x = a + b := by linarith
      rw [show x = a + b by linarith [h7]] at h₁ h₂
      have h8 : 2 * a^2 + 3 * a * b + 2 * b^2 = 0 := by
        nlinarith
      have h9 : b^2 ≤ 0 := by
        nlinarith [sq_nonneg (2 * a + 3 * b / 2)]
      have h10 : b = 0 := by nlinarith [sq_nonneg b]
      have h11 : a = 0 := by
        rw [h10] at h8
        nlinarith
      simp [h11, h10]
  · -- Show that (0, 0) works
    rintro ⟨rfl, rfl⟩
    use 0
    constructor
    · -- Check first equation
      norm_num
    · -- Check second equation
      norm_num