import Mathlib

theorem algebra_211587 {p q : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (A B C α β γ : ℝ) (h1 : ∀ x y, (p * x + (1 - p) * y) ^ 2 = A * x ^ 2 + B * x * y + C * y ^ 2)
    (h2 : ∀ x y, (p * x + (1 - p) * y) * (q * x + (1 - q) * y) = α * x ^ 2 + β * x * y + γ * y ^ 2) :
    max (max A B) C ≥ 4 / 9 ∧ max (max α β) γ ≥ 4 / 9 := by
  have hp0 : 0 ≤ p := hp.1 
  have hp1 : p ≤ 1 := hp.2 
  have hq0 : 0 ≤ q := hq.1 
  have hq1 : q ≤ 1 := hq.2 
  have eq1 := h1 1 0
  have eq2 := h1 0 1
  have eq3 := h1 1 1
  have eq4 := h2 1 0
  have eq5 := h2 0 1
  have eq6 := h2 1 1
  have hA : A = p ^ 2 := by
    ring_nf at eq1 ⊢
    nlinarith 
  have hC : C = (1 - p) ^ 2 := by 
    ring_nf at eq2 ⊢
    nlinarith 
  have hB : B = 2 * p * (1 - p) := by 
    rw [hA, hC] at eq3 
    ring_nf at eq3 ⊢ 
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hα : α = p * q := by 
    ring_nf at eq4 ⊢ 
    nlinarith 
  have hγ : γ = (1 - p) * (1 - q) := by 
    ring_nf at eq5 ⊢ 
    nlinarith 
  have hβ : β = p * (1 - q) + (1 - p) * q := by 
    rw [hα, hγ] at eq6
    ring_nf at eq6 ⊢ 
    nlinarith [sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2)]
  have h1' : max (max A B) C ≥ 4 / 9 := by 
    by_contra h
    push_neg at h
    have h1 : max (max A B) C < 4 / 9 := by
      simpa using h 
    have hA1 : A < 4 / 9 := by 
      have h14 : max (max A B) C ≥ A := by 
        simp [max_le_iff]
      nlinarith 
    have hB1 : B < 4 / 9 := by 
      have h14 : max (max A B) C ≥ B := by 
        simp [max_le_iff]
      nlinarith 
    have hC1 : C < 4 / 9 := by 
      have h14 : max (max A B) C ≥ C := by 
        simp [max_le_iff]
      nlinarith 
    rw [hA] at hA1 
    rw [hB] at hB1
    rw [hC] at hC1 
    nlinarith [sq_nonneg (p - 1 / 3), sq_nonneg (p - 2 / 3), 
      mul_nonneg (show (0 : ℝ) ≤ p by linarith) (show (0 : ℝ) ≤ 1 - p by linarith)
    ]
  have h2' : max (max α β) γ ≥ 4 / 9 := by 
    by_contra h 
    push_neg at h 
    have h1 : max (max α β) γ < 4 / 9 := by 
      simpa using h 
    have hA1 : α < 4 / 9 := by 
      have h14 : max (max α β) γ ≥ α := by 
        simp [max_le_iff]
      nlinarith 
    have hB1 : β < 4 / 9 := by 
      have h14 : max (max α β) γ ≥ β := by 
        simp [max_le_iff]
      nlinarith 
    have hC1 : γ < 4 / 9 := by 
      have h14 : max (max α β) γ ≥ γ := by 
        simp [max_le_iff]
      nlinarith 
    rw [hα] at hA1 
    rw [hβ] at hB1 
    rw [hγ] at hC1 
    nlinarith [sq_nonneg (p - q), sq_nonneg (p - (2 / 3)), sq_nonneg (q - (2 / 3)), sq_nonneg (p - 1 / 3), sq_nonneg (q - 1 / 3), 
      mul_nonneg (show (0 : ℝ) ≤ p by linarith) (show (0 : ℝ) ≤ 1 - p by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ q by linarith) (show (0 : ℝ) ≤ 1 - q by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ p by linarith) (show (0 : ℝ) ≤ q by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ 1 - p by linarith) (show (0 : ℝ) ≤ 1 - q by linarith)
    ]
  constructor 
  · exact h1'
  · exact h2'