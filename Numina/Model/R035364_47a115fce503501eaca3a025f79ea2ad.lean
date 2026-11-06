import Mathlib

theorem algebra_600457 {p q : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (A B C α β γ : ℝ) (h1 : ∀ x y : ℝ, (p * x + (1 - p) * y) ^ 2 = A * x ^ 2 + B * x * y + C * y ^ 2)
    (h2 : ∀ x y : ℝ, (p * x + (1 - p) * y) * (q * x + (1 - q) * y) = α * x ^ 2 + β * x * y + γ * y ^ 2) :
    max (max A B) C ≥ 4 / 9 ∧ max (max α β) γ ≥ 4 / 9 := by

  have hA : A = p ^ 2 := by
    specialize h1 1 0
    nlinarith

  have hC : C = (1 - p) ^ 2 := by
    specialize h1 0 1
    nlinarith

  have hB : B = 2 * p * (1 - p) := by
    specialize h1 1 1
    rw [hA, hC] at h1
    nlinarith

  have hα : α = p * q := by
    specialize h2 1 0
    nlinarith

  have hγ : γ = (1 - p) * (1 - q) := by
    specialize h2 0 1
    nlinarith

  have hβ : β = p * (1 - q) + q * (1 - p) := by
    specialize h2 1 1
    rw [hα, hγ] at h2
    nlinarith

  have h3 : max (max A B) C ≥ 4 / 9 := by
    rw [hA, hB, hC]
    rcases hp with ⟨hp0, hp1⟩
    by_cases h1 : p ^ 2 ≥ 2 * p * (1 - p)
    · -- if $p ^ 2 \geq 2 * p * (1 - p)$, then max A B = p ^ 2.
      have h1' : max (p ^ 2) (2 * p * (1 - p)) = p ^ 2 := by apply max_eq_left h1
      by_cases h2 : p ^ 2 ≥ (1 - p) ^ 2
      · -- max (p ^ 2) ((1 - p) ^ 2) = p ^ 2.
        have h2' : max (p ^ 2) ((1 - p) ^ 2) = p ^ 2 := by apply max_eq_left h2
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (p * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 1 / 3)), sq_nonneg ((1 - p) * (1 / 2 - p))]
      · -- max (p ^ 2) ( (1 - p) ^ 2) = (1 - p) ^ 2.
        have h2' : max (p ^ 2) ((1 - p) ^ 2) = (1 - p) ^ 2 := by apply max_eq_right (by nlinarith)
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (p * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 1 / 3)), sq_nonneg ((1 - p) * (1 / 2 - p))]
    · -- else max A B = 2 * p * (1 - p).
      have h1' : max (p ^ 2) (2 * p * (1 - p)) = 2 * p * (1 - p) := by
        apply max_eq_right
        nlinarith
      by_cases h2 : 2 * p * (1 - p) ≥ (1 - p) ^ 2
      · -- max (2 * p * (1 - p)) ( (1 - p) ^ 2) = 2 * p * (1 - p).
        have h2' : max (2 * p * (1 - p)) ((1 - p) ^ 2) = 2 * p * (1 - p) := by
          apply max_eq_left
          nlinarith
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (p * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 1 / 3)), sq_nonneg ((1 - p) * (1 / 2 - p))]
      · -- max (2 * p * (1 - p)) ( (1 - p) ^ 2) = (1 - p) ^ 2.
        have h2' : max (2 * p * (1 - p)) ((1 - p) ^ 2) = (1 - p) ^ 2 := by
          apply max_eq_right
          nlinarith
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (p * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 2 / 3)), sq_nonneg ((1 - p) * (p - 1 / 3)), sq_nonneg ((1 - p) * (1 / 2 - p))]
  
  have h4 : max (max α β) γ ≥ 4 / 9 := by 
    rw [hα, hβ, hγ]
    rcases hp with ⟨hp0, hp1⟩
    rcases hq with ⟨hq0, hq1⟩
    by_cases h1 : p * q ≥ p * (1 - q) + q * (1 - p)
    · -- max (p*q) (p*(1-q) + q*(1-p)) = p*q.
      have h1' : max (p * q) (p * (1 - q) + q * (1 - p)) = p * q := by apply max_eq_left h1
      by_cases h2 : p * q ≥ (1 - p) * (1 - q)
      · -- max (pq) ((1-p)(1-q)) = pq.
        have h2' : max (p * q) ((1 - p) * (1 - q)) = p * q := by apply max_eq_left h2
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (q - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (q - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hq0), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith)), mul_nonneg (sub_nonneg.mpr hq0) (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith))]
      · -- max (pq) ( (1-p)(1-q)) = (1-p)(1-q).
        have h2' : max (p * q) ((1 - p) * (1 - q)) = (1 - p) * (1 - q) := by apply max_eq_right (by nlinarith)
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (q - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (q - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hq0), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith)), mul_nonneg (sub_nonneg.mpr hq0) (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith))]
    · -- max (p*q) (p*(1-q) + q*(1-p)) = p*(1 - q) + q*(1 - p).
      have h1' : max (p * q) (p * (1 - q) + q * (1 - p)) = p * (1 - q) + q * (1 - p) := by
        apply max_eq_right 
        nlinarith
      by_cases h2 : p * (1 - q) + q * (1 - p) ≥ (1 - p) * (1 - q)
      · -- max ( β ) ( γ ) = β.
        have h2' : max (p * (1 - q) + q * (1 - p)) ((1 - p) * (1 - q)) = p * (1 - q) + q * (1 - p) := by
          apply max_eq_left
          nlinarith
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (q - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (q - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hq0), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith)), mul_nonneg (sub_nonneg.mpr hq0) (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith))]
      · -- max ( β ) ( γ ) = γ.
        have h2' : max (p * (1 - q) + q * (1 - p)) ((1 - p) * (1 - q)) = (1 - p) * (1 - q) := by
          apply max_eq_right 
          nlinarith
        rw [h1', h2']
        nlinarith [sq_nonneg (p - 2 / 3), sq_nonneg (q - 2 / 3), sq_nonneg (p - 1 / 3), sq_nonneg (q - 1 / 3), sq_nonneg (p - 1 / 2), sq_nonneg (q - 1 / 2), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr hq0), mul_nonneg (sub_nonneg.mpr hp0) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith)), mul_nonneg (sub_nonneg.mpr hq0) (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)), mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - p by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - q by linarith))]
  
  exact ⟨h3, h4⟩