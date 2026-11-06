import Mathlib

open Real

theorem algebra_278150 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (factors : Finset ℝ)
    (hpos : ∀ x ∈ factors, 0 < x) :
    logb a (∏ x ∈ factors, x) = ∑ x ∈ factors, logb a x := by
  have h5 : log (∏ x ∈ factors, x) = ∑ x ∈ factors, log x := by
    have h6 : ∀ x ∈ factors, (0 : ℝ) < x := hpos
    have h5b : log (∏ i in factors, (i : ℝ)) = ∑ i in factors, log (i : ℝ) := by
      apply Real.log_prod
      intro i hi
      have h7 : (i : ℝ) > 0 := by
        have h8 : i ∈ factors := by 
          simpa using hi
        apply hpos i h8
      linarith
    simpa using h5b
  have h8 : logb a (∏ x ∈ factors, x) = log (∏ x in factors, x) / log a := by
    field_simp [logb]
  have h9a : log a ≠ 0 := by
    have ha1 : a > 0 := ha.1
    have ha2 : a ≠ 1 := ha.2
    exact log_ne_zero_of_pos_of_ne_one ha1 ha2
  have h9 : ∑ x in factors, logb a x = ∑ x in factors, (log x / log a) := by 
    apply Finset.sum_congr
    · 
      rfl
    · 
      intro x hx
      have h9'' : logb a x = log x / log a := by 
        field_simp [logb]
      rw [h9'']
  rw [h8]
  rw [h5, h9]
  <;> try { simp [Finset.sum_div, h9a] }