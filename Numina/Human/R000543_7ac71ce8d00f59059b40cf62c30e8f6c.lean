import Mathlib

/- Let $x^2+bx+c = 0$ be a quadratic whose roots are each two more than the roots of $3x^2-5x-7$. What is $c$? -/
theorem algebra_12246 {b c : ℝ} (h : ∀ x, x ^ 2 + b * x + c = 0 ↔ 3 * (x - 2) ^ 2 - 5 * (x - 2) - 7 = 0) :
    c = 5 := by
  -- Show that 3 * x * x - 17 * x + 15 = 0 has a solution. This equation is equal to 3 * (x - 2) ^ 2 - 5 * (x - 2) - 7).
  have g : ∃ x : ℝ, 3 * x * x + (-17) * x + 15 = 0 := by
    have g₁ : ∃ s : ℝ, discrim 3 (-17) 15 = s * s := by
      use Real.sqrt 109
      rw [discrim.eq_1]
      norm_num
    apply @exists_quadratic_eq_zero at g₁
    obtain ⟨x₁, g₁⟩ := g₁
    use x₁
    linarith
    norm_num
  obtain ⟨x₁, g⟩ := g
  have k := g
  rw [show 3 * x₁ * x₁ + -17 * x₁ + 15 = 3 * (x₁ - 2) ^ 2 - 5 * (x₁ - 2) - 7 by ring] at g
  rw [(h x₁).symm] at g
  rw [show x₁ ^ 2 + b * x₁ + c = x₁ * x₁ - (-b) * x₁ + c by ring] at g
  have g₀ := g
  -- Apply Vieta formula to get another root satisfying the equation.
  apply vieta_formula_quadratic at g
  obtain ⟨x₂, g₁, g_sum, g_prod⟩ := g
  -- Factorize x ^ 2 + b * x + c.
  have h₀ {x : ℝ}: x ^ 2 + b * x + c = (x - x₁) * (x - x₂) := by
    ring_nf
    simp [g_prod]
    rw [show -(x * x₁) - x * x₂ = -x * (x₁ + x₂) by ring]
    simp [g_sum]
  conv at h =>
    intro x
    rw [h₀]
  -- Do the same thing with the equation 3 * x * x - 17 * x + 15 = 0.
  rw [show 3 * x₁ * x₁ + -17 * x₁ + 15 = (x₁ * x₁ - (17 / 3) * x₁ + (15 / 3)) * 3 by ring, show (0 : ℝ) = 0 * 3 by norm_num] at k
  apply mul_right_cancel₀ at k
  have k₀ := k
  apply vieta_formula_quadratic at k
  obtain ⟨y, k₁, k_sum, k_prod⟩ := k
  -- Factorize 3 * (x - 2) ^ 2 - 5 * (x - 2) - 7.
  have h₁ {x : ℝ}: 3 * (x - 2) ^ 2 - 5 * (x - 2) - 7 = 3 * (x - x₁) * (x - y) := by
    ring_nf
    simp [k_prod]
    rw [show -(x * x₁ * 3) - x * y * 3 = -x * (x₁ + y) * 3 by ring]
    simp [k_sum]
    ring_nf
  conv at h =>
    intro x
    rw [h₁]
  -- Show that y = x₂.
  have h₀ : y = x₂ := by
    rw [show y * y - 17 / 3 * y + 15 / 3 = (3 * (y - 2) ^ 2 - 5 * (y - 2) - 7) / 3 by ring] at k₁
    simp at k₁
    rw [h₁] at k₁
    rw [(h y).symm] at k₁
    rw [mul_eq_zero] at k₁
    obtain k₁ | k₁ := k₁
    . replace k₁ : x₁ = y := by
        linarith only [k₁]
      rw [k₁] at k_sum k_prod
      nlinarith only [k_sum, k_prod]
    . linarith only [k₁]
  rw [h₀] at k_sum k_prod
  rw [k_sum] at g_sum
  rw [k_prod] at g_prod
  linarith only [g_prod]
  norm_num
