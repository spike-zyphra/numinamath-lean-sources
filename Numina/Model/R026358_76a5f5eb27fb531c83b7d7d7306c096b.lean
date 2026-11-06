import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

open Real

lemma lemma_1 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, (a i)^2 / b i ≥ (∑ i, a i)^2 / ∑ i, b i := by
  have h1 : ∀ i, 0 < b i := hb
  have h2 : ∑ i : Fin n, (a i)^2 / b i ≥ (∑ i : Fin n, a i)^2 / ∑ i : Fin n, b i := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    have hbi : 0 < b i := hb i
    positivity
  exact h2


theorem inequalities_129735 {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ)
    (hx : ∀ i : Fin n, 0 < x i) (hy : ∀ i : Fin n, 0 < y i)
    (hsum : ∑ i : Fin n, x i = ∑ i : Fin n, y i) :
    ∑ i : Fin n, (x i) ^ 2 / (x i + y i) ≥ (∑ i : Fin n, x i) / 2 := by
  have h1 : ∀ i : Fin n, 0 < x i + y i := by
    intro i
    have hx2 : 0 < x i := hx i
    have hy2 : 0 < y i := hy i
    linarith
  have h3 : ∑ i : Fin n, (x i + y i) = 2 * (∑ i : Fin n, x i) := by
    calc
      ∑ i : Fin n, (x i + y i) = ∑ i : Fin n, (x i) + ∑ i : Fin n, (y i) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, x i) + (∑ i : Fin n, x i) := by
        have h4 : ∑ i : Fin n, (y i) = ∑ i : Fin n, x i := by
          linarith [hsum]
        rw [h4]
      _ = 2 * (∑ i : Fin n, x i) := by
        ring

  have h2 : ∑ i : Fin n, (x i) ^ 2 / (x i + y i) ≥ (∑ i : Fin n, x i) ^ 2 / ∑ i : Fin n, (x i + y i) := by
    let a := fun (i : Fin n) => x i
    let b := fun (i : Fin n) => x i + y i
    apply lemma_1 n hn a b
    · intro i
      exact hx i
    · -- Show ∀ i, 0 < b i
      intro i
      have h7 : 0 < x i + y i := h1 i
      exact h7

  have h4 : (∑ i : Fin n, x i) ^ 2 / ∑ i : Fin n, (x i + y i) = (∑ i : Fin n, x i) / 2 := by
    rw [h3]
    have h5 : (∑ i : Fin n, x i) ≥ 0 := by
      apply Finset.sum_nonneg
      intro i hi
      have hx6 : 0 < x i := hx i
      linarith
    have hx5 : (∑ i : Fin n, x i) > 0 := by
      have h57 : (∑ i : Fin n, x i) > 0 := by
        apply Finset.sum_pos
        · intro i hi
          exact hx i
        · use ⟨0, by omega⟩
          simp
      linarith
    field_simp [show (∑ i : Fin n, x i) ≠ 0 by linarith]
    <;> ring_nf
  linarith [h2, h4]