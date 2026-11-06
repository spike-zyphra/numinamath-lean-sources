import Mathlib

open Real

-- Let (p₁, ..., pᵣ) and (q₁, ..., qᵣ) be two probability distributions. Show that the following Gibbs' inequality holds: -∑_{i=1}^r pᵢ ln pᵢ ≤ -∑_{i=1}^r pᵢ ln qᵢ
theorem inequalities_180544
    (r : ℕ)
    (hr : 0 < r)
    (p q : Fin r → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioc 0 1)
    (hq : ∀ i, q i ∈ Set.Ioc 0 1)
    (hsum : ∑ i, p i = 1 ∧ ∑ i, q i = 1) :
    - ∑ i, p i * log (p i) ≤ - ∑ i, p i * log (q i) := by

  have hp1 : ∀ i, 0 < p i := by
    intro i
    have h1 := hp i
    exact h1.left

  have hq1 : ∀ i, 0 < q i := by
    intro i
    have h1 := hq i
    exact h1.left

  have h1 : ∀ i : Fin r, log (q i) - log (p i) ≤ (q i / p i) - 1 := by
    intro i
    have hp2 : p i > 0 := hp1 i
    have hq2 : q i > 0 := hq1 i

    have h2 : log (q i) - log (p i) = log (q i / p i) := by
      rw [log_div (by linarith) (by linarith)]

    rw [h2] at *

    have h3 : log (q i / p i) ≤ (q i / p i) - 1 := by
      have h4 : q i / p i > 0 := by
        apply div_pos
        linarith
        linarith
      have h5 : log (q i / p i) ≤ (q i / p i) - 1 := by
        linarith [Real.log_le_sub_one_of_pos h4]
      linarith

    linarith

  have h2 : ∀ i : Fin r, p i * (log (q i) - log (p i)) ≤ q i - p i := by
    intro i
    have hp2 : p i > 0 := hp1 i
    have hq2 : q i > 0 := hq1 i

    have h3 := h1 i

    have h4 : p i * (log (q i) - log (p i)) ≤ p i * ((q i / p i) - 1) := by
      have h5 : log (q i) - log (p i) ≤ (q i / p i) - 1 := by
        linarith [h3]
      nlinarith [h5, hp2]

    have h5 : p i * ((q i / p i) - 1) = q i - p i := by
      field_simp [show p i ≠ 0 by linarith]
      <;> nlinarith

    nlinarith [h4, h5]

  have h3 : ∑ i : Fin r, p i * (log (q i) - log (p i)) ≤ ∑ i : Fin r, (q i - p i) := by
    apply Finset.sum_le_sum
    intro i hi
    specialize h2 i
    simpa using h2

  have h4 : ∑ i : Fin r, (q i - p i) = 0 := by
    have h5 : ∑ i : Fin r, q i = 1 := hsum.right
    have h6 : ∑ i : Fin r, p i = 1 := hsum.left
    calc
      ∑ i : Fin r, (q i - p i) = ∑ i : Fin r, q i - ∑ i : Fin r, p i := by
        rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by
        rw [h5, h6]
      _ = 0 := by
        norm_num

  have h5 : ∑ i : Fin r, p i * (log (q i) - log (p i)) =
          (∑ i : Fin r, p i * log (q i)) - (∑ i : Fin r, p i * log (p i)) := by
    simp [Finset.sum_sub_distrib, mul_sub]

  -- Rearranging the terms to give the final result
  linarith [h3, h4, h5]