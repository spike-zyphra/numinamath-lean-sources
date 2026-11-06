import Mathlib

theorem algebra_259646 {x y : ℤ} (h : x^2 * y^2 = x^2 + y^2) :
    x = 0 ∧ y = 0 := by
  have h2 : (x^2 - 1) * (y^2 - 1) = 1 := by
    nlinarith
  have h4 : (x^2 - 1) = 1 ∨ (x^2 - 1) = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h2
  cases h4 with
  | inl h5 =>
    -- This would lead to x^2 = 2, which is impossible
    have h6 : x^2 = 2 := by
      omega
    exfalso 
    have h7 : x ≤ 1 := by nlinarith [show x ^ 2 ≥ 0 from by nlinarith, h6]
    have h8 : x ≥ -1 := by nlinarith [show x ^ 2 ≥ 0 from by nlinarith, h6]
    interval_cases x <;> try { 
      omega
    }
    <;> try { 
      norm_num at h6 
      all_goals try { contradiction }
    }
  | inr h5 =>
    -- If x^2 -1=-1 => x^2=0 => x=0
    have hx : x = 0 := by
      nlinarith
    -- From h2:
    -- (x^2 - 1)*(y^2 - 1) =1
    -- (-1)*(y^2 -1) =1
    -- so y^2 -1 = -1
    -- => y^2 = 0
    -- => y = 0
    have h8 : (y^2 - 1) = -1 := by 
      rw [show x^2 - 1 = -1 by nlinarith [h5]] at h2 
      linarith
    have hy : y = 0 := by 
      nlinarith
    exact ⟨hx, hy⟩