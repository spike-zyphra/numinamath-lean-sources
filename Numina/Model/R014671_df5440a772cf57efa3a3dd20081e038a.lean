import Mathlib

theorem algebra_108275 {x y z k : ℝ} (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x)
    (h₃ : x^3 + y^3 + k * (x^2 + y^2) = 2008) (h₄ : y^3 + z^3 + k * (y^2 + z^2) = 2008)
    (h₅ : z^3 + x^3 + k * (z^2 + x^2) = 2008) :
    x * y * z = 1004 := by
  have eq1 : x^3 + y^3 + k * (x^2 + y^2) = y^3 + z^3 + k * (y^2 + z^2) := by
    linarith
  have eq2 : x^3 - z^3 + k * (x^2 - z^2) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
      intro h'
      apply h₀
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by
      intro h'
      apply h₁
      linarith
    ), sq_pos_of_ne_zero (show z - x ≠ 0 by
      intro h'
      apply h₂
      linarith
    )]
  have eq3 : (x - z) * (x^2 + x * z + z^2 + k * (x + z)) = 0 := by
    ring_nf at eq2 ⊢
    <;> nlinarith
  have h₆ : x^2 + x * z + z^2 + k * (x + z) = 0 := by
    apply (mul_left_inj' (show x - z ≠ 0 by
      intro h'
      apply h₂
      linarith
    )).mp
    linarith
  have eq4 : z^3 + x^3 + k * (z^2 + x^2) - (x^3 + y^3 + k * (x^2 + y^2)) = 0 := by
    linarith
  have eq5 : z^3 - y^3 + k * (z^2 - y^2) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h'
      apply h₀
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by
      intro h'
      apply h₁
      linarith
    ), sq_pos_of_ne_zero (show z - x ≠ 0 by
      intro h'
      apply h₂
      linarith
    )]
  have eq6 : (z - y) * (z^2 + z * y + y^2 + k * (z + y)) = 0 := by
    ring_nf at eq5 ⊢
    <;> nlinarith
  have h₇ : z^2 + z * y + y^2 + k * (z + y) = 0 := by
    apply (mul_left_inj' (show z - y ≠ 0 by
      intro h'
      apply h₁
      linarith
    )).mp
    linarith
  have eq6 : (x - y) * (x + y + z + k) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by
      intro h'
      apply h₀
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by
      intro h'
      apply h₁
      linarith
    ), sq_pos_of_ne_zero (show z - x ≠ 0 by
      intro h'
      apply h₂
      linarith
    )]
  have h₈ : x + y + z + k = 0 := by
    apply (mul_left_inj' (show x - y ≠ 0 by
      intro h'
      apply h₀
      linarith
    )).mp
    linarith
  have hk : k = - (x + y + z) := by
    linarith
  rw [hk] at h₃ h₄ h₅
  nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
    intro h'
    apply h₀
    linarith
  ), sq_pos_of_ne_zero (show y - z ≠ 0 by 
    intro h'
    apply h₁
    linarith
  ), sq_pos_of_ne_zero (show z - x ≠ 0 by 
    intro h'
    apply h₂
    linarith
  ), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]