import Mathlib

theorem algebra_170071 (t : ℕ) (ht : t > 0) (h : ∑ i ∈ Finset.range t, (50 + 5 * i) = 175 + 40 * t) :
    t = 7 := by
  have eq1 : ∀ t : ℕ, ∑ i in Finset.range t, (50 + 5 * i) = 50 * t + 5 * (t * (t - 1) / 2) := by 
    intro t 
    induction t with 
    | zero =>
      simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      cases t with
      | zero => 
        simp 
      | succ t => 
        simp [Nat.mul_add, Nat.add_mul, mul_add] at *
        all_goals 
          ring_nf at *
          <;> omega 
  have eq2 := eq1 t 
  rw [eq2] at h 
  have h1 : t ≤ 14 := by 
    by_contra h5 
    push_neg at h5 
    have h5' : t ≥ 15 := by omega 
    have h8 : 50 * t + 5 * (t * (t - 1) / 2) > 175 + 40 * t := by 
      have h9 : t ≥ 15 := h5' 
      have h10 : t * (t - 1) / 2 ≥ 105 := by 
        have h11 : t - 1 ≥ 14 := by 
          omega 
        have h12 : t ≥ 15 := by 
          omega 
        have h13 : t * (t - 1) ≥ 15 * 14 := by 
          nlinarith [show t ≥ 15 by omega, show t - 1 ≥ 14 by omega] 
        omega 
      omega 
    omega 
  interval_cases t <;> norm_num at h ⊢ <;> omega