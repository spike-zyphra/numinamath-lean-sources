import Mathlib

open Real

theorem inequalities_145434 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (h₀ : ∑ i : Fin n, (a i)^2 ≤ 1) (h₁ : ∑ i : Fin n, (b i)^2 ≤ 1) :
    (1 - ∑ i : Fin n, a i * b i)^2 ≥ (1 - ∑ i : Fin n, (a i)^2) * (1 - ∑ i : Fin n, (b i)^2) := by
  have h3 : 0 ≤ ∑ i : Fin n, ((a i) - (b i)) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    positivity

  have h6 : ∑ i : Fin n, ((a i) - (b i)) ^ 2 = (∑ i : Fin n, (a i) ^ 2) + (∑ i : Fin n, (b i) ^ 2) - 2 * (∑ i : Fin n, (a i) * (b i)) := by
    have h7 : ∀ i : Fin n, ((a i) - (b i)) ^ 2 = (a i) ^ 2 + (b i) ^ 2 - 2 * ((a i) * (b i)) := by
      intro i
      ring
    calc
      ∑ i : Fin n, ((a i) - (b i)) ^ 2 = ∑ i : Fin n, ((a i) ^ 2 + (b i) ^ 2 - 2 * ((a i) * (b i))) := by
        apply Finset.sum_congr
        . rfl
        intro i _
        specialize h7 i
        linarith
      _ = (∑ i : Fin n, (a i) ^ 2) + (∑ i : Fin n, (b i) ^ 2) - 2 * (∑ i : Fin n, ((a i) * (b i)) ) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ i : Fin n, (a i) ^ 2) + (∑ i : Fin n, (b i) ^ 2) - 2 * (∑ i : Fin n, (a i) * (b i)) := by 
        all_goals ring

  have h2 : (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq

  nlinarith [sq_nonneg ((∑ i : Fin n, (a i) ^ 2) - (∑ i : Fin n, (b i) ^ 2)), sq_nonneg ((∑ i : Fin n, (a i) * (b i)) - (∑ i : Fin n, (a i) ^ 2)), sq_nonneg ((∑ i : Fin n, (a i) * (b i)) - (∑ i : Fin n, (b i) ^ 2)), sq_nonneg ((∑ i : Fin n, ((a i) - (b i)) ^ 2)), sq_nonneg ((∑ i : Fin n, (a i)^2) + (∑ i : Fin n, (b i)^2) - 2)]