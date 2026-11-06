import Mathlib

theorem algebra_96688 (θ : ℝ) (h : ∑' n : ℕ, (Real.cos θ)^(2 * n) = 5) :
Real.cos (2 * θ) = 3/5 := by 
  have h1 : ∑' n : ℕ, (Real.cos θ)^(2 * n) = ∑' n : ℕ, ( (Real.cos θ)^2 )^n := by 
    congr 
    funext n 
    ring 
  rw [h1] at h 
  have h2 : ( (Real.cos θ) ^ 2 ) < 1 := by 
    by_contra h2
    push_neg at h2 
    have h3 : ( (Real.cos θ) ^ 2 ) ≥ 1 := by nlinarith 
    have h4 : ¬ Summable (fun (n : ℕ) => ( (Real.cos θ)^2 )^n ) := by 
      by_contra h5 
      have h5 : Summable (fun (n : ℕ) => ( (Real.cos θ)^2 )^n ) := h5 
      have h8 := summable_geometric_iff_norm_lt_one.mp h5 
      norm_num [abs_lt] at h8 ⊢ 
      all_goals 
        nlinarith 
    have h4 := h4 
    have h4' : (∑' n : ℕ, ( (Real.cos θ)^2 )^n ) = 0 := by 
      rw [tsum_eq_zero_of_not_summable h4] 
    linarith [h, h4']
  have h1_sum : ∑' n : ℕ, ( (Real.cos θ)^2 )^n = 1 / (1 - ( (Real.cos θ) ^ 2 ) ) := by 
    rw [tsum_geometric_of_lt_one] 
    all_goals 
    try { 
      ring_nf 
    } 
    all_goals 
      nlinarith [h2] 
  rw [h1_sum] at h 
  have h3 : 1 / (1 - ( (Real.cos θ) ^ 2 ) ) = 5 := h 
  have h4_ne : (1 - ( (Real.cos θ) ^ 2 ) ) ≠ 0 := by 
    by_contra h4_0 
    have h_zero1 : 1 - ( (Real.cos θ) ^ 2 ) = 0 := h4_0 
    rw [h_zero1] at h3 
    norm_num [h_zero1] at h3 
  have h5 : (1 - ( (Real.cos θ) ^ 2 ) ) = (1 / 5 : ℝ) := by 
    field_simp [h4_ne] at h3 
    linarith 
  have h6 : ( (Real.cos θ) ^ 2 ) = (4 / 5 : ℝ) := by 
    nlinarith 
  have h7 : Real.cos (2 * θ) = 2 * ( (Real.cos θ) ^ 2 ) - 1 := by 
    rw [Real.cos_two_mul] 
  rw [h7] 
  rw [h6] 
  all_goals 
    norm_num