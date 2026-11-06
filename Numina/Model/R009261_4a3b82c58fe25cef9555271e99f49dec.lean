import Mathlib

theorem algebra_10473 :  {x : ℝ | ∃ a : ℝ, a ≠ 0 ∧ (a * x^2 + 20 * x + 7 = 0) ∧ (∀ y : ℝ, a * y^2 + 20 * y + 7 = 0 → y = x)} = {-(7/10)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, show that if x is in the left set, then x = -7/10
    rintro ⟨a, ha_ne_zero, h₁, h₂⟩
    have h4 : ∀ y : ℝ, a * y^2 + 20 * y + 7 = 0 → y = x := h₂
    have h_eq1 : a * (- (20 / a) - x)^2 + 20 * (- (20 / a) - x) + 7 = 0 := by
      have h1 : a ≠ 0 := ha_ne_zero
      have h_eq2 : a * (- (20 / a) - x)^2 + 20 * (- (20 / a) - x) + 7 = 
        ( a * ((- (20 / a) - x)^2) ) + 20 * (- (20 / a) - x) + 7 := by 
          ring
      rw [h_eq2]
      have h2 : a * ((- (20 / a) - x)^2) = ((-20 - a * x) ^ 2) / a := by
        field_simp [h1]
        <;> ring
      rw [h2]
      have h3 : (-20 - a * x) ^ 2 = 400 + 40 * (a * x) + (a * x)^2 := by
        ring_nf 
      rw [h3]
      field_simp [h1]
      <;> nlinarith [h₁, sq_nonneg (a * x + 10), sq_nonneg (x), sq_nonneg (a * x + 14 / 10), sq_nonneg (x + 7 / 10)]
    have h_eq2 := h4 (- (20 / a) - x) h_eq1
    have h_eq3 : - (20 / a) - x = x := by
      linarith [h_eq2]
    field_simp [ha_ne_zero] at h_eq3 
    nlinarith [h₁, h_eq3, sq_nonneg (a * x + 10), sq_nonneg (x + 7 / 10)]
  · -- Now that we have proven that direction, prove the reverse direction
    intro hx
    rw [hx]
    use 100 / 7
    constructor
    · -- Show a is non zero 
      norm_num 
    constructor
    · -- Show that 100/7 * x^2 + 20*x + 7 = 0
      norm_num 
    · -- Show that the solution is unique
      intro y hy
      have h_eq : 100 / 7 * y^2 + 20 * y + 7 = 0 := by 
        linarith [hy]
      have h₁ : (y + 7 / 10) ^ 2 = 0 := by 
        nlinarith 
      have h₂ : y + 7 / 10 = 0 := by 
        nlinarith [sq_nonneg (y + 7 / 10)]
      linarith