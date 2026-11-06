import Mathlib

theorem algebra_253390 :
    {x : ℝ | 0 < x ∧ 3 * x ^ Real.logb 5 2 + 2 ^ Real.logb 5 x = 64} = {625} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- Assume $x$ is in the set. Then $0 < x$ and $3x^{\log_5 2} + 2^{\log_5 x} = 64$. Show $x = 625$.
    rintro ⟨hx, heq⟩
    have h2 : x ^ Real.logb 5 2 = (2 : ℝ) ^ Real.logb 5 x := by 
      have h3 : Real.log (x ^ Real.logb 5 2) = Real.log ( (2 : ℝ) ^ Real.logb 5 x ) := by
        have h4 : Real.log (x ^ Real.logb 5 2) = Real.logb 5 2 * Real.log x := by 
          rw [Real.log_rpow]
          all_goals linarith
        have h5 : Real.log ( (2 : ℝ) ^ Real.logb 5 x ) = Real.logb 5 x * Real.log (2 : ℝ) := by 
          rw [Real.log_rpow]
          all_goals linarith
        rw [h4, h5]
        have h6 : Real.logb 5 2 = Real.log (2) / Real.log (5) := by 
          field_simp [Real.logb]
        have h7 : Real.logb 5 x = Real.log x / Real.log (5) := by 
          field_simp [Real.logb]
        rw [h6, h7]
        <;> field_simp <;> ring
      have h9 : x ^ Real.logb 5 2 = (2 : ℝ) ^ Real.logb 5 x := by 
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h3
      linarith 
    rw [h2] at heq
    have h3 : (2 : ℝ) ^ Real.logb 5 x = (16 : ℝ) := by
      nlinarith 
    have h4 : Real.logb 5 x = (4 : ℝ) := by
      have h5 : (2 : ℝ) ^ Real.logb 5 x = (16 : ℝ) := h3 
      have h7 : (2 : ℝ) ^ (Real.logb 5 x) = (2 : ℝ) ^ (4 : ℝ) := by 
        rw [h5]
        norm_num
      have h8 : Real.logb 5 x = (4 : ℝ) := by
        apply_fun (Real.logb (2 : ℝ)) at h7
        simp at h7 ⊢
        all_goals linarith
      exact h8 
    have h7 : x = (625 : ℝ) := by 
      have h8 : Real.logb 5 x = (4 : ℝ) := h4 
      have h9 : x = (5 : ℝ) ^ Real.logb 5 x := by 
        field_simp at *
      rw [h8] at h9 
      norm_num at h9 ⊢
      linarith 
    linarith 
  · -- Assume $x = 625$. Show $0 < x ∧ 3 * x ^ Real.logb 5 2 + 2 ^ Real.logb 5 x = 64$.
    intro h1 
    rw [h1] 
    constructor
    · -- Show $0 < (625 : ℝ)$
      norm_num 
    · -- Show $3 * (625 : ℝ) ^ Real.logb 5 2 + 2 ^ Real.logb 5 (625 : ℝ) = 64$
      have h11 : Real.logb 5 (625 : ℝ) = (4 : ℝ) := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      have h12 : (625 : ℝ) ^ Real.logb 5 2 = (16 : ℝ) := by
        have h31 : Real.logb 5 (625 : ℝ) = (4 : ℝ) := h11
        have h32 : (625 : ℝ) ^ Real.logb 5 2 = ((5 : ℝ)  ^ (4 : ℝ)) ^ Real.logb 5 2 := by
          norm_num 
        rw [h32]
        have h33 : ((5 : ℝ) ^ (4 : ℝ)) ^ Real.logb 5 2 = (5 : ℝ) ^ (4 * Real.logb 5 2 : ℝ) := by 
          rw [← Real.rpow_mul]
          ring 
          all_goals norm_num 
        rw [h33]
        have h34 : (5 : ℝ) ^ (4 * Real.logb 5 2) = ((5 : ℝ) ^ Real.logb 5 2) ^ (4 : ℝ) := by
          rw [← Real.rpow_mul]
          ring 
          all_goals norm_num 
        rw [h34]
        have h35 : (5 : ℝ) ^ Real.logb 5 2 = (2 : ℝ) := by 
          rw [Real.rpow_logb]
          all_goals norm_num 
        rw [h35]
        norm_num 
      have h13 : (2 : ℝ) ^ Real.logb 5 (625 : ℝ) = (16 : ℝ) := by 
        rw [h11] 
        norm_num 
      rw [h12, h13] 
      all_goals norm_num