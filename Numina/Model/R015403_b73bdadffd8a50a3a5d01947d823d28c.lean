import Mathlib

theorem algebra_196706 (α β γ : ℝ) (h : (1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ) =
    (1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ)) :
    (1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ) = abs (Real.cos α * Real.cos β * Real.cos γ) ∧
    (1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ) = abs (Real.cos α * Real.cos β * Real.cos γ) := by

  have h1 : (1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ) ≥ 0 := by
    apply mul_nonneg
    apply mul_nonneg
    · -- Show that $1 - \sin \alpha \geq 0$
      linarith [show Real.sin α ≤ 1 by apply Real.sin_le_one, show -1 ≤ Real.sin α by linarith [Real.neg_one_le_sin α, Real.sin_le_one α]]
    · -- Show that $1 - \sin \beta \geq 0$
      linarith [show Real.sin β ≤ 1 by apply Real.sin_le_one, show -1 ≤ Real.sin β by linarith [Real.neg_one_le_sin β, Real.sin_le_one β]]
    · -- Show that $1 - \sin \gamma \geq 0$
      linarith [show Real.sin γ ≤ 1 by apply Real.sin_le_one, show -1 ≤ Real.sin γ by linarith [Real.neg_one_le_sin γ, Real.sin_le_one γ]]

  have h2 : (1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ) ≥ 0 := by
    apply mul_nonneg
    apply mul_nonneg
    · -- Show that $1 + \sin \alpha \geq 0$
      linarith [show Real.sin α ≤ 1 by apply Real.sin_le_one, show -1 ≤ Real.sin α by linarith [Real.neg_one_le_sin α, Real.sin_le_one α]]
    · -- Show that $1 + \sin \beta \geq 0$
      linarith [show Real.sin β ≤ 1 by apply Real.sin_le_one, show -1 ≤ Real.sin β by linarith [Real.neg_one_le_sin β, Real.sin_le_one β]]
    · -- Show that $1 + \sin \gamma \geq 0$
      linarith [show Real.sin γ ≤ 1 by apply Real.sin_le_one, show -1 ≤ Real.sin γ by linarith [Real.neg_one_le_sin γ, Real.sin_le_one γ]]

  have h3 : ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) * ((1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ)) =
          (Real.cos α * Real.cos β * Real.cos γ) ^ 2 := by
    ring_nf
    have h4 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    have h5 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    have h6 : Real.cos γ ^ 2 + Real.sin γ ^ 2 = 1 := Real.cos_sq_add_sin_sq γ
    have h7 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
      linarith
    have h8 : Real.cos β ^ 2 = 1 - Real.sin β ^ 2 := by 
      linarith
    have h9 : Real.cos γ ^ 2 = 1 - Real.sin γ ^ 2 := by
      linarith
    rw [h7, h8, h9]
    <;> nlinarith [Real.sin_sq_le_one α, Real.sin_sq_le_one β, Real.sin_sq_le_one γ]

  have hEq : (1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ) = abs (Real.cos α * Real.cos β * Real.cos γ) := by
    have h4 : ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) ^ 2 = (Real.cos α * Real.cos β * Real.cos γ) ^ 2 := by
      have h5 : ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) * ((1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ)) =
          (Real.cos α * Real.cos β * Real.cos γ) ^ 2 := h3
      have h6 : (1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ) = (1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ) := by linarith [h]
      calc 
        ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) ^ 2 = ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) * ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) := by ring
        _ = ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) * ((1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ)) := by rw [h6]
        _ = (Real.cos α * Real.cos β * Real.cos γ) ^ 2 := by rw [h5]
    
    have h8 : ((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) ≥ 0 := h1

    have h9 : abs (Real.cos α * Real.cos β * Real.cos γ) = Real.sqrt ((Real.cos α * Real.cos β * Real.cos γ) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    
    have h10 : Real.sqrt ((Real.cos α * Real.cos β * Real.cos γ) ^ 2) = Real.sqrt (((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) ^ 2) := by 
      rw [h4]
    
    have h11 : Real.sqrt (((1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ)) ^ 2) = (1 - Real.sin α) * (1 - Real.sin β) * (1 - Real.sin γ) := by
      rw [Real.sqrt_sq (by linarith [h1])]

    rw [h9, h10, h11]

  have hEq2 : (1 + Real.sin α) * (1 + Real.sin β) * (1 + Real.sin γ) = abs (Real.cos α * Real.cos β * Real.cos γ) := by
    linarith [h, hEq]

  constructor
  · exact hEq
  · exact hEq2