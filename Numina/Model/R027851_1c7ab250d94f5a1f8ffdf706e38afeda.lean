import Mathlib

open Real

theorem algebra_195132 {n : ℕ} (hn : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = 2014 ↔ n = 4060224 := by
  constructor 
  · -- Proof for forward direction
    intro h 
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1)) ) = Real.sqrt (↑n + 1) - 1 := by 
      intro n 
      induction n with 
      | zero => 
        simp 
        <;> norm_num 
      | succ n ih => 
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr (show (↑n + 1 : ℝ) > 0 by positivity), Real.sqrt_pos.mpr (show (↑n + 1 + 1 : ℝ) > 0 by positivity)]
        <;> ring_nf <;> field_simp 
        <;> ring_nf <;> norm_num 
        <;> ring 
    have h2 : (Real.sqrt (↑n + 1) - 1 : ℝ) = (2014 : ℝ) := by
      specialize h1 n 
      linarith 
    have h3 : Real.sqrt (↑n + 1 : ℝ) = (2015 : ℝ) := by
      nlinarith 
    have h4 : (↑n + 1 : ℝ) = (2015 : ℝ) ^ 2 := by
      calc 
        (↑n + 1 : ℝ) = (Real.sqrt (↑n + 1 : ℝ)) ^ 2 := by 
          rw [Real.sq_sqrt]
          positivity 
        _ = (2015 : ℝ) ^ 2 := by 
          rw [h3]
    have h5 : (↑n + 1 : ℕ) = 2015 ^ 2 := by 
      exact_mod_cast h4 
    have h6 : n = 4060224 := by 
      norm_num at h5 
      omega 
    assumption
  · -- Proof for backward direction 
    intro h 
    rw [h]
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1)) ) = Real.sqrt (↑n + 1) - 1 := by 
      intro n 
      induction n with 
      | zero => 
        simp 
        <;> norm_num 
      | succ n ih => 
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr (show (↑n + 1 : ℝ) > 0 by positivity), Real.sqrt_pos.mpr (show (↑n + 1 + 1 : ℝ) > 0 by positivity)]
        <;> ring_nf <;> field_simp 
        <;> ring_nf <;> norm_num 
        <;> ring 
    have eq1 : ∑ i ∈ Finset.Icc 1 (4060224 : ℕ), (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (↑4060224 + 1) - 1 := by
      specialize h1 4060224
      simpa using h1
    rw [eq1]
    have h5 : Real.sqrt (↑4060224 + 1 : ℝ) = (2015 : ℝ) := by 
      rw [show (↑4060224 + 1 : ℝ) = (2015 : ℝ)^2 by norm_num]
      rw [Real.sqrt_sq (by norm_num)]
      <;> norm_num 
    rw [h5]
    all_goals norm_num 
    <;> ring_nf <;> norm_num 
    all_goals ring
  all_goals norm_num 
  all_goals ring_nf <;> norm_num 
  all_goals ring 
  all_goals norm_num 
  all_goals ring_nf <;> norm_num 
  all_goals ring