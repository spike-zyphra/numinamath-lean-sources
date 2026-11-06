import Mathlib

theorem algebra_8963 (A B C D E : ℝ) (hA : A ≠ 0) (hroots : {α, β, γ, δ} = {x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0}) (hroots' : {α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} = {x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0}) :
    3 * (B + C + D) / A = 85 := by
  have h1 : (α : ℝ) ∈ ({α, β, γ, δ} : Set ℝ) := by simp
  have h2 : (α : ℝ) ∈ ({x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} : Set ℝ) := by
    rw [show {x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} = {α, β, γ, δ} by rw [hroots]] 
    exact h1
  have h3 : 3 * α ^ 4 + 9 * α ^ 2 + 5 = 0 := by 
    simpa using h2
  have h4 : (β : ℝ) ∈ ({α, β, γ, δ} : Set ℝ) := by simp
  have h5 : (β : ℝ) ∈ ({x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} : Set ℝ) := by
    rw [show {x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} = {α, β, γ, δ} by rw [hroots]] 
    exact h4
  have h6 : 3 * β ^ 4 + 9 * β ^ 2 + 5 = 0 := by 
    simpa using h5
  have h7 : (γ : ℝ) ∈ ({α, β, γ, δ} : Set ℝ) := by simp
  have h8 : (γ : ℝ) ∈ ({x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} : Set ℝ) := by
    rw [show {x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} = {α, β, γ, δ} by rw [hroots]] 
    exact h7
  have h9 : 3 * γ ^ 4 + 9 * γ ^ 2 + 5 = 0 := by 
    simpa using h8
  have h10 : (δ : ℝ) ∈ ({α, β, γ, δ} : Set ℝ) := by simp
  have h11 : (δ : ℝ) ∈ ({x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} : Set ℝ) := by
    rw [show {x | 3 * x ^ 4 + 9 * x ^ 2 + 5 = 0} = {α, β, γ, δ} by rw [hroots]] 
    exact h10
  have h12 : 3 * δ ^ 4 + 9 * δ ^ 2 + 5 = 0 := by 
    simpa using h11

  have h13 : α ^ 2 ∈ ({α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} : Set ℝ) := by simp
  have h14 : α ^ 2 ∈ ({x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} : Set ℝ) := by
    rw [show {x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} = {α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} by rw [hroots']]
    exact h13
  have h15 : A * (α ^ 2) ^ 4 + B * (α ^ 2) ^ 3 + C * (α ^ 2) ^ 2 + D * (α ^ 2) + E = 0 := by 
    simpa using h14

  have h16 : β ^ 2 ∈ ({α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} : Set ℝ) := by simp
  have h17 : β ^ 2 ∈ ({x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} : Set ℝ) := by
    rw [show {x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} = {α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} by rw [hroots']]
    exact h16
  have h18 : A * (β ^ 2) ^ 4 + B * (β ^ 2) ^ 3 + C * (β ^ 2) ^ 2 + D * (β ^ 2) + E = 0 := by 
    simpa using h17

  have h19 : γ ^ 2 ∈ ({α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} : Set ℝ) := by simp
  have h20 : γ ^ 2 ∈ ({x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} : Set ℝ) := by
    rw [show {x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} = {α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} by rw [hroots']]
    exact h19
  have h21 : A * (γ ^ 2) ^ 4 + B * (γ ^ 2) ^ 3 + C * (γ ^ 2) ^ 2 + D * (γ ^ 2) + E = 0 := by 
    simpa using h20

  have h22 : δ ^ 2 ∈ ({α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} : Set ℝ) := by simp
  have h23 : δ ^ 2 ∈ ({x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} : Set ℝ) := by
    rw [show {x | A * x ^ 4 + B * x ^ 3 + C * x ^ 2 + D * x + E = 0} = {α ^ 2, β ^ 2, γ ^ 2, δ ^ 2} by rw [hroots']]
    exact h22
  have h24 : A * (δ ^ 2) ^ 4 + B * (δ ^ 2) ^ 3 + C * (δ ^ 2) ^ 2 + D * (δ ^ 2) + E = 0 := by 
    simpa using h23

  ring_nf at h15 h18 h21 h24 
  ring_nf at h3 h6 h9 h12 
  field_simp at *
  nlinarith [sq_pos_of_ne_zero hA, sq_nonneg (α ^ 2), sq_nonneg (β ^ 2), sq_nonneg (γ ^ 2), sq_nonneg (δ ^ 2),
    sq_nonneg (α ^ 2 - β ^ 2), sq_nonneg (α ^ 2 - γ ^ 2), sq_nonneg (α ^ 2 - δ ^ 2), 
    sq_nonneg (β ^ 2 - γ ^ 2), sq_nonneg (β ^ 2 - δ ^ 2), sq_nonneg (γ ^ 2 - δ ^ 2)]