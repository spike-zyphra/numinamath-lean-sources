import Mathlib

open Real

theorem inequalities_79565 (n : ℕ) (x : Fin n → ℝ)
    (h₀ : ∀ i, 0 < x i) (h₁ : ∑ i, x i ≤ ∑ i, (x i)^2) :
    ∀ t > 1, ∑ i, (x i)^t ≤ ∑ i, (x i)^(t + 1) := by 
  intro t ht
  have h3 : ∀ i, (x i : ℝ) ^ t * ((x i) - 1) ≥ (x i : ℝ) * ((x i) - 1) := by
    intro i
    by_cases h : (x i) ≥ (1 : ℝ)
    · -- Case where x i ≥1
      have h6 : (x i : ℝ) ^ t ≥ (x i : ℝ) := by
        have h2 : (x i : ℝ) ≥ (1 : ℝ) := h
        have h33 : t ≥ 1 := by linarith
        have h4 : (x i : ℝ) ^ t ≥ (x i : ℝ) ^ 1 := by 
          apply pow_le_pow_right 
          all_goals 
            nlinarith [show (0 : ℝ) ≤ (x i : ℝ) by linarith [h₀ i]]
        have h55 : (x i : ℝ) ^ 1 = (x i : ℝ) := by
          simp
        calc
          (x i : ℝ) ^ t ≥ (x i : ℝ) ^ 1 := by linarith [h4]
          _ = (x i : ℝ) := by linarith [h55]
      have h7 : (x i : ℝ) ^ t * ((x i) - 1) ≥ (x i : ℝ) * ((x i) - 1) := by 
        have h8 : (x i : ℝ) - 1 ≥ 0 := by
          nlinarith
        nlinarith [h6, h8]
      linarith
    · -- x i <1
      have h8 : (x i : ℝ) < (1 : ℝ) := by linarith
      have h9 : (x i : ℝ) ^ t ≤ (x i : ℝ) := by 
        have h21 : (x i : ℝ) < (1 : ℝ) := h8
        have h22 : t ≥ 1 := by linarith
        have h10 : (x i : ℝ) ^ t ≤ (x i : ℝ) ^ 1 := by 
          apply pow_le_pow_of_le_one 
          all_goals 
            nlinarith [show (0 : ℝ) ≤ (x i : ℝ) by linarith [h₀ i]]
        have h55 : (x i : ℝ) ^ 1 = (x i : ℝ) := by
          simp
        calc 
          (x i : ℝ) ^ t ≤ (x i : ℝ) ^ 1 := by linarith [h10]
          _ = (x i : ℝ) := by linarith [h55]
      have h10 : (x i : ℝ) ^ t * ((x i) - 1) ≥ (x i : ℝ) * ((x i) - 1) := by 
        have h111 : (x i : ℝ) - 1 < (0 : ℝ) := by 
          linarith 
        nlinarith [h9, h111]
      linarith 
  have eq1 : ∑ i, ((x i) ^ t * ((x i) - 1)) = ∑ i, ((x i) ^ (t + 1) - (x i) ^ t) := by 
    congr
    funext i
    ring_nf 
  have eq2 : ∑ i, (x i * ((x i) - 1)) = ∑ i, ((x i) ^ 2 - x i) := by
    congr
    funext i
    ring_nf
  have h5 : ∑ i, ((x i) ^ t * ((x i) - 1)) ≥ ∑ i, (x i * ((x i) - 1)) := by 
    apply Finset.sum_le_sum 
    intro i hi
    have h66 : (x i : ℝ) ^ t * ((x i) - 1) ≥ (x i : ℝ) * ((x i) - 1) := h3 i 
    linarith
  have h6 : ∑ i, (x i * ((x i) - 1)) ≥ 0 := by
    have h7 : ∑ i, (x i * ((x i) - 1)) = (∑ i, (x i)^2) - (∑ i, x i) := by 
      rw [eq2]
      simp [Finset.sum_sub_distrib]
    nlinarith [h₁, h7]
  have eq3 : ∑ i, ((x i) ^ (t + 1) - (x i) ^ t) = (∑ i, (x i) ^ (t + 1)) - (∑ i, (x i) ^ t) := by 
    simp [Finset.sum_sub_distrib]
  have h8 : (∑ i, (x i) ^ (t + 1)) - (∑ i, (x i) ^ t) ≥ 0 := by
    calc 
      (∑ i, (x i) ^ (t + 1)) - (∑ i, (x i) ^ t) = ∑ i, ((x i) ^ t * ((x i) - 1)) := by 
        rw [eq1] 
        <;> simp [Finset.sum_sub_distrib]
      _ ≥ ∑ i, (x i * ((x i) - 1)) := by 
        linarith [h5]
      _ ≥ (0 : ℝ) := by 
        linarith [h6]
  linarith [h8]