import Mathlib

theorem algebra_38074 (x : ℝ) :
    ∑ i ∈ Finset.range 1996, (x ^ 2 + (i + 1) * x + (i + 1 - 1)) ^ 2 = 0 ↔ x = -1 := by
  constructor
  · -- First direction: if the sum is zero then x = -1
    rintro h
    have h74 : ∀ i : ℕ, i < 1996 → (x ^ 2 + (i + 1) * x + (i + 1 - 1)) ^ 2 = 0 := by
      have h9 : ∑ i ∈ Finset.range 1996, (x ^ 2 + (i + 1) * x + (i + 1 - 1)) ^ 2 = 0 := h
      have h3 : ∀ i ∈ Finset.range 1996, (x ^ 2 + (i + 1) * x + (i + 1 - 1)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
            nlinarith [sq_nonneg (x ^ 2 + (i + 1) * x + (i + 1 - 1))]
          ) |>.mp h9
      intro i hi
      specialize h3 i (by simp at hi ⊢; exact_mod_cast hi)
      exact_mod_cast h3
    -- This implies that each term must be zero.
    have term_nonneg : ∀ i : ℕ, i < 1996 → x ^ 2 + (i + 1) * x + (i + 1 - 1) = 0 := by
      intro i hi
      -- For each term, squared_eq_zero implies...
      have squared_eq_zero := h74 i hi
      have : (x ^ 2 + (i + 1) * x + (i + 1 - 1)) ^ 2 = 0 := by linarith 
      have : x ^ 2 + (i + 1) * x + (i + 1 - 1) = 0 := by
        nlinarith
      exact_mod_cast this
    have nonneg_0 : x ^ 2 + x = 0 := by 
      specialize term_nonneg 0 (by norm_num)
      norm_num at term_nonneg ⊢
      linarith
    -- This gives x=0 or x=-1
    have nonneg_00 := nonneg_0
    -- Now we'll need more... constrain x to a single value
    have nonneg_1 : x = -1 := by 
      specialize term_nonneg 1 (by norm_num)
      norm_num at term_nonneg ⊢
      have h6 : x = -1 := by
        nlinarith
      assumption
    assumption
  · -- Second direction: if x = -1 then sum = 0
    intro h
    rw [h]
    norm_num 
    <;> 
    ring