import Mathlib

open Real
open scoped BigOperators

theorem inequalities_599443 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (h : ∑ i, a i = ∑ i, b i) :
  ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
  -- We first establish that for each i, a_i + b_i > 0.
  have h11 : ∀ i : Fin n, 0 < a i + b i := by
    intro i
    have ha1 : 0 < a i := ha i
    have hb1 : 0 < b i := hb i
    linarith
  have h15 : ∑ i, ((a i)^2 / (a i + b i) + (b i)^2 / (a i + b i)) ≥ ∑ i, (a i + b i) / 2 := by
    apply Finset.sum_le_sum 
    intro i hi
    have h14 : (a i)^2 / (a i + b i) + (b i)^2 / (a i + b i) ≥ (a i + b i) / 2 := by
      have h15 : 0 < a i + b i := h11 i
      have h16 : (a i)^2 / (a i + b i) + (b i)^2 / (a i + b i) - (a i + b i) / 2 ≥ 0 := by
        have h17 : (a i)^2 / (a i + b i) + (b i)^2 / (a i + b i) - (a i + b i) / 2 =
            (2 * (a i)^2 + 2 * (b i)^2 - (a i + b i)^2) / (2 * (a i + b i)) := by 
            field_simp
            <;> ring
        rw [h17]
        apply div_nonneg
        -- Show that $2(a_i^2 + b_i^2) \ge (a_i + b_i)^2$
        nlinarith [sq_nonneg (a i - b i)]
        -- Show that denominator $2(a_i + b_i)$ is positive
        positivity 
      linarith
    linarith 
  have h17 : ∑ i, (a i + b i) / 2 = (∑ i, a i) := by
    have h100 : ∑ i, (a i + b i) / 2 = (∑ i, (a i + b i)) / 2 := by 
      rw [Finset.sum_div]
    have h101 : ∑ i, (a i + b i) = (∑ i, a i) + (∑ i, b i) := by
      simp [Finset.sum_add_distrib]
    have h102 : (∑ i, a i) + (∑ i, b i) = 2 * (∑ i, a i) := by
      have h00 : (∑ i, b i) = (∑ i, a i) := by 
        linarith [h]
      linarith [h00]
    rw [h100, h101, h102]
    <;> linarith 
  have h16 : ∑ i, ((a i)^2 / (a i + b i) + (b i)^2 / (a i + b i)) =
      ∑ i, (a i)^2 / (a i + b i) + ∑ i, (b i)^2 / (a i + b i) := by
    simp [Finset.sum_add_distrib]
  have h18 : (∑ i, (a i)^2 / (a i + b i)) + (∑ i, (b i)^2 / (a i + b i)) ≥ (∑ i, a i) := by
    linarith [h15, h16, h17]
  have h23 : ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
    have h24 : (∑ i, (a i) ^ 2 / (a i + b i)) ≥ (∑ i, a i) / 2 := by 
      have h25 : (∑ i, (a i) ^ 2 / (a i + b i)) ≥ (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) := by 
        apply Finset.sq_sum_div_le_sum_sq_div
        all_goals 
          intro i hi
          specialize h11 i 
          positivity
      have h26 : (∑ i, (a i + b i)) = 2 * (∑ i, a i) := by 
        have h27 : ∑ i, (a i + b i) = (∑ i, a i) + (∑ i, b i) := by 
          simp [Finset.sum_add_distrib]
        have h28 : (∑ i, b i) = (∑ i, a i) := by 
          linarith [h]
        rw [h27, h28]
        linarith 
      have h27 : (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) = (∑ i, a i) / 2 := by
        rw [h26]
        have h28 : (∑ i, a i) ≠ 0 := by
          by_contra h0
          have h00 : (∑ i, a i) = 0 := by linarith 
          have h01 : n = 0 := by
            have : (∑ i, a i) > 0 := by 
              apply Finset.sum_pos
              · -- Show that each term in the sum is positive
                intro i hi
                specialize ha i 
                positivity 
              · -- Show that the set is non-empty
                use ⟨0, by linarith [hn]⟩
                simp 
            linarith -- contradiction
          linarith -- contradiction with hn 
        field_simp [h28]
        <;> nlinarith 
      linarith [h25, h27]
    linarith [h24]
  linarith [h23]