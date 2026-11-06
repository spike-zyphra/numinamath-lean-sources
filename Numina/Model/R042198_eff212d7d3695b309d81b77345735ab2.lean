import Mathlib

theorem algebra_252641 :
  { (a, b, c) : ℝ × ℝ × ℝ | ∃ x1 x2 x3 : ℝ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧ 
    a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0 ∧ a * x3 ^ 2 + b * x3 + c = 0 } = { (0, 0, 0) } := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (a, b, c) ∈ { (a, b, c) | ∃ three distinct x1, x2, x3 satisfying the equations }
    rintro ⟨x1, x2, x3, hx12, hx23, hx31, heq1, heq2, heq3⟩
    have eq1 : a * x1 ^ 2 + b * x1 + c = 0 := heq1
    have eq2 : a * x2 ^ 2 + b * x2 + c = 0 := heq2
    have eq3 : a * x3 ^ 2 + b * x3 + c = 0 := heq3

    have eq4 : a * x1 ^ 2 + b * x1 + c - (a * x2 ^ 2 + b * x2 + c) = 0 := by linarith
    have eq5 : a * (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by
      nlinarith
    have eq6 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
      ring_nf at eq5 ⊢
      <;> linarith

    have h1 : a * (x1 + x2) + b = 0 := by
      apply (mul_left_inj' (show x1 - x2 ≠ 0 by
        intro h
        apply hx12
        linarith 
      )).mp
      linarith

    have eq7 : a * x2 ^ 2 + b * x2 + c - (a * x3 ^ 2 + b * x3 + c) = 0 := by linarith 
    have eq8 : a * (x2 ^ 2 - x3 ^ 2) + b * (x2 - x3) = 0 := by
      nlinarith 
    have eq9 : (x2 - x3) * (a * (x2 + x3) + b) = 0 := by
      ring_nf at eq8 ⊢ 
      <;> linarith

    have h2 : a * (x2 + x3) + b = 0 := by
      apply (mul_left_inj' (show x2 - x3 ≠ 0 by
        intro h 
        apply hx23 
        linarith 
      )).mp
      linarith

    have h3 : a * (x1 - x3) = 0 := by
      linarith

    have h_a : a = 0 := by 
      apply (mul_left_inj' (show x1 - x3 ≠ 0 by
        intro h 
        apply hx31 
        linarith 
      )).mp 
      linarith

    have h_b : b = 0 := by
      rw [h_a] at h1 
      linarith

    have h_c : c = 0 := by 
      rw [h_a, h_b] at eq1 
      linarith

    simp [h_a, h_b, h_c]

  · -- Assume (a, b, c) = (0, 0, 0)
    rintro ⟨rfl, rfl, rfl⟩ 
    use (1 : ℝ)
    use (2 : ℝ)
    use (3 : ℝ)
    constructor 
    · -- Check x1 ≠ x2
      norm_num 
    constructor
    · -- Check x2 ≠ x3 
      norm_num 
    constructor 
    · -- Check x3 ≠ x1 
      norm_num
    constructor
    · -- Check the equation for x1 
      norm_num 
    constructor 
    · -- Check the equation for x2 
      norm_num 
    · -- Check the equation for x3 
      norm_num