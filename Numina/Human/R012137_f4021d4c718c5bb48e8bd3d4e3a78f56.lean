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
      simp
      have hppos : ∀ i, p i > 0 := by
        intro i
        have := hp i
        simp at this
        linarith
      have hqpos : ∀ i, q i > 0 := by
        intro i
        have := hq i
        simp at this
        linarith
      have : ∑ i : Fin r, p i * log (q i) - ∑ i : Fin r, p i * log (p i) ≤ 0 := by
        calc
          _ = ∑ i : Fin r, (p i * log (q i) - p i * log (p i)) := by
            exact Eq.symm Finset.sum_sub_distrib
          -- Note that, due to the properties of the logarithmic function, the inequality to be proved is equivalent to ∑_{i=1}^{r} p_i ln(q_i / p_i) ≤ 0
          _ = ∑ i : Fin r, (p i * log ((q i)/(p i))) := by
            congr
            ext i
            rw [← mul_sub_left_distrib]
            rw [← log_div]
            · have := hqpos i
              linarith
            · have := hppos i
              linarith
          -- We use the inequality ln x ≤ x - 1, which is valid for any positive x. Then ∑_{i=1}^{r} p_i ln(q_i / p_i) ≤ ∑_{i=1}^{r} p_i (q_i / p_i - 1) = ∑_{i=1}^{r} (q_i - p_i) = 0
          _ ≤ ∑ i : Fin r, (p i * ((q i)/(p i) - 1)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hdivpos : (q i) / (p i) > 0 := by
              exact div_pos (hqpos i) (hppos i)
            have := @log_le_sub_one_of_pos ((q i)/(p i)) hdivpos
            exact (mul_le_mul_iff_of_pos_left (hppos i)).mpr this
          _ = ∑ i : Fin r, (q i - p i) := by
            congr
            ext i
            rw [mul_sub_left_distrib]
            field_simp
            apply mul_div_cancel_left₀ (q i)
            have := hppos i
            linarith
          _ = _ := by
            rw [Finset.sum_sub_distrib, hsum.1, hsum.2]
            simp
      linarith
