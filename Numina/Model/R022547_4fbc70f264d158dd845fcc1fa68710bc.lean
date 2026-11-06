import Mathlib

open Real

theorem inequalities_261335 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by

  have h1 : ∀ i, 0 < a i + b i := by
    intro i
    have ha_i : 0 < a i := ha i
    have hb_i : 0 < b i := hb i
    linarith

  have h2 : ∑ i : Fin n, (a i) ^ 2 / (a i + b i) ≥ (∑ i : Fin n, a i) ^ 2 / (∑ i : Fin n, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    have ha_i : 0 < a i := ha i
    have hb_i : 0 < b i := hb i
    have h1_i : 0 < a i + b i := by linarith
    simpa using h1_i

  have h3 : (∑ i : Fin n, (a i + b i)) = 2 * (∑ i : Fin n, a i) := by
    calc
      (∑ i : Fin n, (a i + b i)) = (∑ i : Fin n, a i) + (∑ i : Fin n, b i) := by
        simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, a i) + (∑ i : Fin n, a i) := by
        rw [show (∑ i : Fin n, b i) = (∑ i : Fin n, a i) by linarith [h]]
      _ = 2 * (∑ i : Fin n, a i) := by
        ring

  by_cases h4 : (∑ i : Fin n, a i) = 0
  · -- Case where $\sum a_i = 0$. This is impossible as $a_i > 0$ and $n \ge 1$.
    have h7 : (∑ i : Fin n, a i) > 0 := by
      have h6 : n ≥ 1 := by linarith
      have h10 : ∃ j : Fin n, a j > 0 := by
        use ⟨0, by linarith⟩
        have h11 : a ⟨0, by linarith⟩ > 0 := ha ⟨0, by linarith⟩
        exact h11
      obtain ⟨j, h11⟩ := h10
      have h13 : (∑ i : Fin n, a i) > 0 := by
        have h14 : (∑ i : Fin n, a i) ≥ a j := by
          apply Finset.single_le_sum (fun i hi => by
            have h12 : a i ≥ 0 := by linarith [ha i]
            linarith
          ) (Finset.mem_univ j)
        have h15 : a j > 0 := h11
        linarith [h15]
      linarith
    linarith [h4, h7]

  · -- Case where $\sum a_i \ne 0$.
    have h6 : (∑ i : Fin n, a i) ≠ 0 := by
      intro h7
      apply h4
      exact h7
    -- Determine $\frac{(\sum a_i)^2}{\sum (a_i + b_i)} = \frac{\sum a_i}{2}$
    have h4' : (∑ i : Fin n, a i) ^ 2 / (∑ i : Fin n, (a i + b i)) = (∑ i : Fin n, a i) / 2 := by
      rw [h3]
      have h7 : (∑ i : Fin n, a i) ≠ 0 := h6
      field_simp
      <;> ring_nf <;> norm_num
    linarith [h2, h4']