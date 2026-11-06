import Mathlib

open Real

theorem algebra_194962 {n : ℕ} (hn : n ≥ 1) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = 2016 ↔ n = 4068288 := by
  constructor
  · -- Assume sum equals 2016, prove n = 4068288
    intro h
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by
      intro n
      induction n with
      | zero =>
        simp [Finset.sum_eq_zero]
        all_goals norm_num
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr]
        <;> ring_nf <;> field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr]
        <;> ring_nf <;> norm_num
        all_goals ring_nf <;> field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr]
        all_goals ring_nf <;> norm_num
    have h2 := h1 n
    rw [h2] at h
    have h_eq1 : sqrt (n + 1) = 2017 := by linarith
    have h_eq2 : (n + 1 : ℝ) = (2017 : ℝ) ^ 2 := by 
      calc
        (n + 1 : ℝ) = (sqrt (n + 1) : ℝ) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (2017 : ℝ) ^ 2 := by rw [h_eq1]
    have h_eq3 : (n : ℝ) = (2017 : ℝ) ^ 2 - 1 := by
      have h_eq4 : (n : ℝ) = (n + 1 : ℝ) - (1 : ℝ) := by ring
      rw [h_eq4, h_eq2]
      all_goals ring
    have h_eq4 : n = 4068288 := by
      have h_eq5 : (n : ℝ) = (4068288 : ℝ) := by
        nlinarith
      have h_eq6 : n = 4068288 := by
        exact_mod_cast h_eq5
      exact h_eq6
    exact h_eq4
  · -- Assume n = 4068288, prove sum equals 2016
    intro h_eq
    rw [h_eq]
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by
      intro n
      induction n with
      | zero =>
        simp [Finset.sum_eq_zero]
        all_goals norm_num
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr]
        <;> ring_nf <;> field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr]
        <;> ring_nf <;> norm_num
        all_goals ring_nf <;> field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr]
        all_goals ring_nf <;> norm_num
    have heq1 := h1 4068288
    rw [heq1]
    have eq : sqrt (↑4068288 + 1 : ℝ) - 1 = (2016 : ℝ) := by
      have h_eq4068289 : sqrt (↑4068288 + 1 : ℝ) = (2017 : ℝ) := by
        have h_eq : (↑4068288 + 1 : ℝ) = (2017 : ℝ) ^ 2 := by
          norm_num
        rw [h_eq]
        rw [Real.sqrt_sq (by norm_num)]
      rw [h_eq4068289]
      all_goals norm_num
    norm_num at eq ⊢
    all_goals nlinarith
    all_goals try { simpa }
    all_goals try { norm_num at * }
    all_goals try { tauto }
    all_goals try { linarith }
    all_goals try { nlinarith }
    all_goals try { try { rfl } }
    all_goals try { tauto }
    all_goals try { linarith }