import Mathlib

theorem algebra_9697 (α β γ : ℝ) (h : α ≠ β ∧ β ≠ γ ∧ α ≠ γ)
    (h1 : 2*α^3+2*α+3=0) (h2 : 2*β^3+2*β+3=0) (h3 : 2*γ^3+2*γ+3=0) :
    4*α^6+8*α^4+4*α^2-9=0 ∧ 4*β^6+8*β^4+4*β^2-9=0 ∧
    4*γ^6+8*γ^4+4*γ^2-9=0 := by
  have eq1 : 2 * α^3 + 2 * α + 3 = 0 := by
    linarith 
  have eq2 : 2 * β^3 + 2 * β + 3 = 0 := by 
    linarith 
  have eq3 : 2 * γ^3 + 2 * γ + 3 = 0 := by 
    linarith 
  -- For α
  have halpha : 4 * α^6 + 8 * α^4 + 4 * α^2 - 9 = 0 := by
    have halpha1 : α^3 = -α - 3 / 2 := by 
      linarith 
    have halpha2 : α^4 = -α^2 - 3 / 2 * α := by
      calc 
        α^4 = α * α^3 := by ring 
        _ = α * (-α - 3 / 2) := by rw [halpha1] 
        _ = -α^2 - 3 / 2 * α := by ring 
    have halpha3 : α^6 = α^2 + 3 * α + 9 / 4 := by 
      calc 
        α^6 = (α^3) ^ 2 := by ring 
        _ = (-α - 3 / 2) ^ 2 := by rw [halpha1] 
        _ = α^2 + 3 * α + 9 / 4 := by ring 
    nlinarith [sq_nonneg (α^2), sq_nonneg (α + 3 / 2)]
  -- For β
  have hbeta : 4 * β^6 + 8 * β^4 + 4 * β^2 - 9 = 0 := by
    have hbeta1 : β^3 = -β - 3 / 2 := by 
      linarith 
    have hbeta2 : β^4 = -β^2 - 3 / 2 * β := by 
      calc 
        β^4 = β * β^3 := by ring 
        _ = β * (-β - 3 / 2) := by rw [hbeta1] 
        _ = -β^2 - 3 / 2 * β := by ring 
    have hbeta3 : β^6 = β^2 + 3 * β + 9 / 4 := by 
      calc 
        β^6 = (β^3) ^ 2 := by ring 
        _ = (-β - 3 / 2) ^ 2 := by rw [hbeta1] 
        _ = β^2 + 3 * β + 9 / 4 := by ring 
    nlinarith [sq_nonneg (β^2), sq_nonneg (β + 3 / 2)]
  -- For γ
  have hgamma : 4 * γ^6 + 8 * γ^4 + 4 * γ^2 - 9 = 0 := by
    have hgamma1 : γ^3 = -γ - 3 / 2 := by 
      linarith 
    have hgamma2 : γ^4 = -γ^2 - 3 / 2 * γ := by 
      calc 
        γ^4 = γ * γ^3 := by ring 
        _ = γ * (-γ - 3 / 2) := by rw [hgamma1] 
        _ = -γ^2 - 3 / 2 * γ := by ring 
    have hgamma3 : γ^6 = γ^2 + 3 * γ + 9 / 4 := by 
      calc 
        γ^6 = (γ^3) ^ 2 := by ring 
        _ = (-γ - 3 / 2) ^ 2 := by rw [hgamma1] 
        _ = γ^2 + 3 * γ + 9 / 4 := by ring 
    nlinarith [sq_nonneg (γ^2), sq_nonneg (γ + 3 / 2)]
  constructor 
  · exact halpha 
  constructor 
  · exact hbeta 
  · exact hgamma