import Mathlib

open Real

theorem inequalities_109941 (n : ℕ) :
    ∏ i ∈ Finset.Icc 2 n, (1 - 1 / (i ^ 2 : ℝ)) > 0.5 := by 
  by_cases h : n = 0 
  · -- empty product, equals 1
    rw [h]
    norm_num [Finset.prod_eq_zero]
  · -- n > 0
    have h2 : n ≥ 1 := by 
      by_contra h
      push_neg at h 
      have h3 : n = 0 := by 
        omega 
      tauto
    have h3 : ∀ (m : ℕ), m ≥ 1 → (∏ i ∈ Finset.Icc 2 m, (1 - 1 / (i ^ 2 : ℝ)) ) = ((m + 1 : ℝ) / (2 * (m : ℝ)) ) := by 
      intro m hm
      induction m with
      | zero => 
        exfalso 
        linarith 
      | succ m' ih =>
        cases m' with 
        | zero => 
          norm_num at ih ⊢
        | succ m => 
          rw [Finset.prod_Icc_succ_top (by linarith)]
          rw [ih (by linarith)]
          field_simp 
          <;> ring_nf 
    have h5 := h3 n h2
    rw [h5] at *
    have h75 : (↑n + 1) / (2 * ↑n) > (1 / 2 : ℝ) := by 
      have hx1 : (2 * (n : ℝ)) > 0 := by 
        have h11 : (n : ℝ) ≥ (1 : ℝ) := by 
          exact_mod_cast h2 
        nlinarith 
      have hx2 : (↑n + 1 : ℝ) > 0 := by 
        have h11 : (n : ℝ) ≥ (1 : ℝ) := by 
          exact_mod_cast h2 
        linarith 
      have hx3 : (↑n + 1 : ℝ) * (2 : ℝ) > (1 : ℝ) * (2 * (↑n : ℝ)) := by
        nlinarith 
      have hx4 : (↑n + 1) / (2 * ↑n) > (1 / 2 : ℝ) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        nlinarith 
      linarith 
    have h76 : (1 / 2 : ℝ) = (0.5 : ℝ) := by norm_num 
    nlinarith [h75, h76]