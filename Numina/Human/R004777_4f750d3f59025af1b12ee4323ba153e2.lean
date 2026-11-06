import Mathlib
/-8. Given $\sin \alpha+\sin \beta=\sin \gamma$, $\cos \alpha+\cos \beta=-\cos \gamma$.
Then $\cos ^{2} \alpha+\cos ^{2} \beta+\cos ^{2} \gamma=$ $\qquad$-/
theorem algebra_321820 (α β γ : ℝ) (h₁ : Real.sin α + Real.sin β = Real.sin γ)
    (h₂ : Real.cos α + Real.cos β = -Real.cos γ) :
    (Real.cos α)^2 + (Real.cos β)^2 + (Real.cos γ)^2 = 3 / 2 := by
--Squaring the given condition, we get $$ \begin{array}{l} \sin ^{2} \alpha+\sin ^{2} \beta+2 \sin \alpha \cdot \sin \beta=\sin ^{2} \gamma, \ \cos ^{2} \alpha+\cos ^{2} \beta+2 \cos \alpha \cdot \cos \beta=\cos ^{2} \gamma . \end{array} $$
  have h3 : Real.sin γ ^ 2 + Real.cos γ ^ 2 = 1 := Real.sin_sq_add_cos_sq γ
  have h4 : (Real.sin α + Real.sin β) ^ 2 = Real.sin γ ^ 2 := by
    rw [h₁]
  have h5 : (Real.cos α + Real.cos β) ^ 2 = Real.cos γ ^ 2 := by
    have h6 : Real.cos α + Real.cos β = -Real.cos γ := h₂
    rw [h6]
    ring
  
  have eq1 : (Real.sin α + Real.sin β) ^ 2 + (Real.cos α + Real.cos β) ^ 2 = Real.sin γ ^ 2 + Real.cos γ ^ 2 := by
    rw [h4, h5]
  
  have eq2 : (Real.sin α + Real.sin β) ^ 2 + (Real.cos α + Real.cos β) ^ 2 = 
            (Real.sin α) ^ 2 + (Real.sin β) ^ 2 + 2 * (Real.sin α * Real.sin β) + (Real.cos α) ^ 2 + (Real.cos β) ^ 2 + 2 * (Real.cos α * Real.cos β) := by 
    ring
  --Adding the two equations yields $\cos (\alpha-\beta)=-\frac{1}{2}$; Subtracting the two equations yields $$ \begin{array}{l} \cos 2 \gamma=\cos 2 \alpha+\cos 2 \beta+2 \cos (\alpha+\beta) \ =2 \cos (\alpha+\beta) \cdot \cos (\alpha-\beta)+2 \cos (\alpha+\beta) \ =\cos (\alpha+\beta) . \end{array} $$
  have h7 : (Real.sin α) ^ 2 + (Real.sin β) ^ 2 + 2 * (Real.sin α * Real.sin β) + (Real.cos α) ^ 2 + (Real.cos β) ^ 2 + 2 * (Real.cos α * Real.cos β) = 1 := by 
    linarith [eq1, h3, eq2]
  
  have h9 : (Real.sin α) ^ 2 + (Real.cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h10 : (Real.sin β) ^ 2 + (Real.cos β) ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  --Therefore, $\cos ^{2} \alpha+\cos ^{2} \beta+\cos ^{2} \gamma$ $$ \begin{array}{l} =\frac{3}{2}+\frac{1}{2}(\cos 2 \alpha+\cos 2 \beta+\cos 2 \gamma) \ =\frac{3}{2}+\frac{1}{2}[2 \cos (\alpha-\beta) \cdot \cos (\alpha+\beta)+\cos 2 \gamma] \ =\frac{3}{2}+\frac{1}{2}[-\cos (\alpha+\beta)+\cos 2 \gamma]=\frac{3}{2} . \end{array} $$
  nlinarith [sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α + Real.cos β), sq_nonneg (Real.sin γ), sq_nonneg (Real.cos γ), h9, h10, h3, h7]