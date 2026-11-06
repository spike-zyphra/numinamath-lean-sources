import Mathlib

theorem algebra_227805 (f : ℝ → ℝ) (h : ∀ x, (f x)^2 ≤ 2 * x^2 * f (x / 2))
    (A : Set ℝ) (hA : A = {x | f x > x^2}) (hA' : A ≠ ∅) :
    ¬Finite A := by
  by_contra h2
  have h3 : Finite A := by 
    simpa using h2 
  -- have h4 : (A : Set ℝ).Finite := by 
  --  simpa using h3 
  -- showing 0 not in A
  have h00 : 0 ∉ A := by 
    by_contra h0 
    have h5 : 0 ∈ A := h0 
    rw [hA] at h5 
    have h5' : f 0 > 0^2 := h5 
    have h6 : f 0^2 ≤ 2 * (0 : ℝ) ^2 * f (0 / 2) := h 0 
    have h7 : f 0^2 ≤ 0 := by 
      nlinarith 
    have h8 : f 0 = 0 := by 
      nlinarith 
    nlinarith 
  -- showing A nonempty
  have h1 : A.Nonempty := by 
    by_contra h1 
    push_neg at h1 
    have h2 : A = ∅ := by 
      ext x 
      simp [hA] at *
      all_goals tauto 
    contradiction 
  -- extracting witness a from nonempty and showing a ≠ 0
  rcases h1 with ⟨a, ha⟩ 
  have ha' : a ∈ A := by
    simpa [hA] using ha
  -- showing a ≠ 0
  have ha_ne0 : a ≠ 0 := by 
    intro h_eq 
    have h0_in : (0 : ℝ) ∈ A := by 
      rw [show (0 : ℝ) = a by linarith [h_eq]] 
      exact ha' 
    contradiction 
  -- have h6 : ∀ (n : ℕ), f (a / 2 ^ n) > (a / 2 ^ n) ^2 := by
  -- have h7 : a ∈ A := ha'
  have h5 : ∀ (n : ℕ), f (a / 2 ^ n) > (a / 2 ^ n) ^2 := by
    intro n 
    induction n with 
    | zero => 
      rw [hA] at ha 
      have : (f a) > (a)^2 := by 
        simpa using ha 
      simpa using this 
    | succ n ih => 
      have h2 := h (a / 2 ^ n) 
      have eq1 : (a / 2 ^ (n + 1 : ℕ)) = (a / 2 ^ n) / 2 := by 
        field_simp [pow_succ] 
        <;> ring 
      rw [eq1] 
      -- have h7 : f ((a / 2 ^ n) / 2) > ((a / 2 ^ n) / 2) ^2 := by
      nlinarith [sq_nonneg (f (a / 2 ^ n) - (a / 2 ^ n) ^ 2), sq_nonneg (f ( (a / 2 ^ n) / 2 ) - ((a / 2 ^ n) / 2) ^ 2), sq_nonneg ((a / 2 ^ n) ^ 2 - f ( (a / 2 ^ n) / 2 ) ), sq_nonneg (f (a / 2 ^ n) ) ]
  -- showing A infinite
  have h6 : ¬ (A : Set ℝ).Finite := by 
    apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => a / 2 ^ n)
    · -- Show function injective 
      intro n m h_eq 
      have h_eq1 : a / (2 : ℝ) ^ n = a / (2 : ℝ) ^ m := by 
        simpa using h_eq 
      by_cases h_a : a ≠ 0 
      · -- Assume a ≠ 0
        have h7 : (2 : ℝ) ^ n = (2 : ℝ) ^ m := by 
          have h8 : a / (2 : ℝ) ^ n = a / (2 : ℝ) ^ m := h_eq1 
          field_simp [(show a ≠ 0 by assumption)] at h8 ⊢ 
          <;> nlinarith 
        have : n = m := by 
          exact Nat.cast_injective (by simpa using h7) 
        assumption 
      · -- Assume a = 0 
        exfalso 
        apply ha_ne0 
        all_goals 
        try contradiction 
        all_goals 
          try tauto 
    · -- Show that for all n, the image is in A 
      intro n 
      have h6n : (a / 2 ^ n) ∈ A := by 
        rw [hA] 
        have h5n : f (a / 2 ^ n) > (a / 2 ^ n) ^2 := h5 n 
        simpa using h5n 
      exact h6n 
  contradiction