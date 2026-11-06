import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_48346 {n : ℕ} (hn : 0 < n) (a b : ℝ)
  (x : Fin n → ℝ) (h₁ : ∀ i, x i ∈ Icc a b) (h₂ : ∑ i, x i = 0) :
  ∑ i, (x i)^2 ≤ -n * a * b := by

  have h3 : ∀ i, a ≤ x i := by 
    intro i 
    have h1' := h₁ i
    exact h1'.1

  have h4 : ∀ i, x i ≤ b := by
    intro i 
    have h1' := h₁ i 
    exact h1'.2

  have h5 : ∀ i, (x i) ^ 2 ≤ (x i) * (a + b) - a * b := by
    intro i
    have h3' : a ≤ x i := h3 i 
    have h4' : x i ≤ b := h4 i 
    have h6 : (x i - a) * (x i - b) ≤ 0 := by
      have h7 : x i - a ≥ 0 := by linarith 
      have h8 : x i - b ≤ 0 := by linarith 
      nlinarith 
    nlinarith

  have h8 : ∑ i, (x i) ^ 2 ≤ ∑ i, ((x i) * (a + b) - a * b) := by 
    apply Finset.sum_le_sum 
    intro i hi
    specialize h5 i 
    linarith

  have h9 : ∑ i, ((x i) * (a + b) - a * b) = (a + b) * (∑ i, (x i)) - n * (a * b) := by 
    have eq1 : ∑ i : Fin n, ((x i) * (a + b) - a * b) = (∑ i : Fin n, (x i * (a + b))) - (∑ i : Fin n, (a * b)) := by 
      simp [Finset.sum_sub_distrib]
    have eq2 : ∑ i : Fin n, (x i * (a + b)) = (a + b) * (∑ i : Fin n, (x i)) := by 
      have h11 : ∀ i : Fin n, x i * (a + b) = (a + b) * (x i) := by 
        intro i 
        ring 
      rw [Finset.sum_congr rfl (fun i _ => h11 i)]
      rw [←Finset.mul_sum]

    have eq3 : ∑ i : Fin n, (a * b) = n * (a * b) := by
      simp [Finset.sum_const, Finset.card_univ]
      <;> ring

    rw [eq1, eq2, eq3]

  rw [h9] at h8 
  rw [h₂] at h8

  have h10 : (a + b) * (0 : ℝ) - n * (a * b) = -n * a * b := by 
    ring

  linarith [h10, h8]