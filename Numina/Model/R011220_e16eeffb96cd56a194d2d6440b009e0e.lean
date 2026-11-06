import Mathlib

open Real

theorem number_theory_613328 (m n k x : ℝ) (hx : x > 0 ∧ x ≠ 1) (hm : m > 0 ∧ m ≠ 1) (hn : n > 0 ∧ n ≠ 1) (hk : k > 0 ∧ k ≠ 1) (h : logb k x - logb m x = logb m x - logb n x) : n ^ 2 = (k * n) ^ (logb k m) := by
  rcases hx with  ⟨hx_pos, hx_ne_1⟩
  rcases hm with  ⟨hm_pos, hm_ne_1⟩
  rcases hn with  ⟨hn_pos, hn_ne_1⟩
  rcases hk with  ⟨hk_pos, hk_ne_1⟩
  have h1 : 2 * logb m x = logb k x + logb n x := by
    linarith
  have h2 : 2 * (log x / log m) = (log x / log k) + (log x / log n) := by
    have h3 : logb m x = log x / log m := by field_simp [logb]
    have h4 : logb k x = log x / log k := by field_simp [logb]
    have h5 : logb n x = log x / log n := by field_simp [logb]
    rw [h3, h4, h5] at h1
    linarith
  have hk_nz : log k ≠ 0 := by
    have hkne1 : k ≠ 1 := hk_ne_1
    have hk_pos2 : k > 0 := hk_pos
    exact log_ne_zero_of_pos_of_ne_one hk_pos2 hkne1
  have hm_nz : log m ≠ 0 := by
    have hmne1 : m ≠ 1 := hm_ne_1
    have hm_pos2 : m > 0 := hm_pos
    exact log_ne_zero_of_pos_of_ne_one hm_pos2 hmne1
  have hn_nz : log n ≠ 0 := by
    have hnne1 : n ≠ 1 := hn_ne_1
    have hn_pos2 : n > 0 := hn_pos
    exact log_ne_zero_of_pos_of_ne_one hn_pos2 hnne1
  have hx_nz : log x ≠ 0 := by
    have hxne1 : x ≠ 1 := hx_ne_1
    have hx_pos2 : x > 0 := hx_pos
    exact log_ne_zero_of_pos_of_ne_one hx_pos2 hxne1
  have h3 : 2 * (1 / log m) = (1 / log k) + (1 / log n) := by
    have h2' : 2 * (log x / log m) = (log x / log k) + (log x / log n) := h2
    have h4 : 2 * (log x / log m) = log x * (2 / log m) := by ring
    have h5 : (log x / log k) + (log x / log n) = log x * (1 / log k + 1 / log n) := by ring
    rw [h4, h5] at h2'
    have h7 : (2 / log m : ℝ) = (1 / log k + 1 / log n : ℝ) := by
      apply (mul_left_inj' hx_nz).mp
      linarith
    field_simp [hk_nz, hm_nz, hn_nz] at h7 ⊢
    nlinarith
  have h10 : 2 * log k * log n = log m * (log k + log n) := by
    field_simp [hk_nz, hm_nz, hn_nz] at h3 ⊢
    nlinarith

  have eq1 : log (n ^ 2) = 2 * log n := by
    simp [log_pow]

  have eq2 : log ((k * n) ^ (logb k m : ℝ)) = logb k m * (log k + log n) := by
    have h13 : log ((k * n) ^ (logb k m : ℝ)) = logb k m * log (k * n) := by
      rw [log_rpow]
      all_goals
        have hk_n : k * n > 0 := mul_pos hk_pos hn_pos
        positivity
    have h14 : log (k * n) = log k + log n := by
      rw [log_mul (by positivity) (by positivity)]
    rw [h14] at h13
    linarith

  have h5 : log (n ^ 2) = log ((k * n) ^ (logb k m : ℝ)) := by
    have eq3 : logb k m = log m / log k := by
      field_simp [logb]
    rw [eq3] at eq2
    have eq4 : log (n ^ 2) = 2 * log n := eq1
    have h9 : (log m / log k) * (log k + log n) = 2 * log n := by
      have h10' : 2 * log k * log n = log m * (log k + log n) := h10
      have hk_nz' : log k ≠ 0 := hk_nz
      field_simp [hk_nz'] at *
      nlinarith
    have eq5 : log ((k * n) ^ (logb k m : ℝ)) = (log m / log k) * (log k + log n) := eq2
    linarith [h9, eq1, eq5]

  have h5' : n ^ 2 > 0 := by positivity
  have h42 : (k * n) ^ (logb k m : ℝ) > 0 := by positivity
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr h5') (Set.mem_Ioi.mpr h42) h5