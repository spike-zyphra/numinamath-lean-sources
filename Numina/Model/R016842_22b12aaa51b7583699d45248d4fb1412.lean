import Mathlib

theorem number_theory_190077 (x y : ℕ) :
    6 * x ^ 2 * y + 2 * x ^ 2 + 3 * x * y + x - 9 * y = 2016 ↔ (x, y) = (4, 20) := by
  constructor
  · -- Assume the equation, prove (x, y) = (4, 20)
    intro h
    have eq1 : 6 * x ^ 2 * y + 2 * x ^ 2 + 3 * x * y + x = 2016 + 9 * y := by
      omega
    have h1 : x ≤ 32 := by
      by_contra h2
      push_neg at h2
      have h8 : x ≥ 33 := by omega
      have h9 : y ≥ 1 := by
        by_contra h9
        push_neg at h9
        have h10 : y = 0 := by linarith
        rw [h10] at h
        have h11 : 2 * x ^ 2 + x = 2016 := by
          nlinarith
        have h12 : x ≤ 32 := by
          nlinarith
        interval_cases x <;> omega
      have h10 : y ≥ 1 := h9
      nlinarith [sq_nonneg (x * y), sq_nonneg (x - 4 : ℤ), sq_nonneg (y - 20 : ℤ)]
    have h20 : y ≤ 100 := by
      have h1 : x ≤ 32 := h1
      interval_cases x <;> omega
    have h4 : x ≤ 32 := h1
    have h5 : y ≤ 100 := h20
    interval_cases x <;> try { 
      omega 
    } <;> norm_num at eq1 ⊢
    <;> try { 
      have h25 : y ≤ 120 := by
        omega 
      interval_cases y <;> norm_num at eq1 ⊢
      <;> tauto 
    }
    <;> try { 
      tauto 
    }
  · -- Show that (4, 20) is a solution
    rintro ⟨rfl, rfl⟩
    all_goals norm_num
    <;> tauto