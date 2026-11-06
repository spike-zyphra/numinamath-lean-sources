import Mathlib

theorem algebra_254429 {n : ℕ} (hn : n ≥ 3) (a b : ℕ → ℝ)
    (h₀ : ∑ i ∈ Finset.range n, a i = ∑ i ∈ Finset.range n, b i)
    (h₁ : 0 < a 0) (h₂ : ∀ i ∈ Finset.range (n - 1), a i = a (i + 1))
    (h₃ : ∀ i ∈ Finset.range (n - 2), a i + a (i + 1) = a (i + 2))
    (h₄ : 0 < b 0) (h₅ : ∀ i ∈ Finset.range (n - 1), b i ≤ b (i + 1))
    (h₆ : ∀ i ∈ Finset.range (n - 2), b i + b (i + 1) ≤ b (i + 2)) :
    a (n - 1) + a (n - 2) ≤ b (n - 1) + b (n - 2) := by
  have h10 : a 0 = a 1 := by
    specialize h₂ 0 (by 
      simp [Finset.mem_range]; 
      all_goals omega
      )
    simpa using h₂
  have h13 : 0 ∈ Finset.range (n - 2) := by 
    simp [Finset.mem_range]; 
    all_goals omega
  have h14 : a 0 + a 1 = a 2 := h₃ 0 (by simp [Finset.mem_range]; all_goals omega)
  have h11 : 1 ∈ Finset.range (n - 1) := by 
    simp [Finset.mem_range];
    all_goals omega
  have h12 : a 1 = a 2 := h₂ 1 (by 
    simp [Finset.mem_range]; 
    all_goals omega
  )
  have h15 : a 2 = a 1 := by
    linarith
  -- substituting we get a 0 = 0 contradicts h 0
  have h16 : a 0 = 0 := by
    nlinarith [h10, h14, h15, h₁]
  -- contradiction
  linarith [h16, h₁]