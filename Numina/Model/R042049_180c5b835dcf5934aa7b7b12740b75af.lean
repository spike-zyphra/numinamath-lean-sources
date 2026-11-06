import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_257049 {a : ℝ} (ha : 0 < a ∧ a ≠ 1)
  (h : ∃ x1 x2 : ℝ, x1 ∈ Ioo 1 3 ∧ x2 ∈ Ioi 6 ∧
    x1^2 - 4 * x1 * logb 2 a + 3 * (logb 2 a)^2 = 0 ∧
    x2^2 - 4 * x2 * logb 2 a + 3 * (logb 2 a)^2 = 0) :
  4 < a ∧ a < 8 := by
  rcases h with ⟨x1, x2, hx1, hx2, heq1, heq2⟩
  rcases hx1 with ⟨hx11, hx12⟩
  have hx21 : 6 < x2 := by
    simpa using hx2
  have h1 : (x1 - logb 2 a) * (x1 - 3 * logb 2 a) = 0 := by 
    nlinarith 
  have h2 : (x2 - logb 2 a) * (x2 - 3 * logb 2 a) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h1) with h3 h4
  · -- Case x1 = logb 2 a 
    have hx1' : x1 = logb 2 a := by linarith
    cases' (mul_eq_zero.mp h2) with h5 h6
    · -- Case x2 = logb 2 a 
      have hx2' : x2 = logb 2 a := by linarith
      nlinarith 
    · -- Case x2 = 3 * logb 2 a 
      have hx2' : x2 = 3 * logb 2 a := by linarith 
      -- Now we know $1 < \ln_2 a < 3$ and $6 <3\ln_2 a$, so $2 < \ln_2 a < 3$.
      -- From that we can prove $4 <a <8$.
      have h21 : 2 < logb 2 a := by 
        nlinarith [hx1', hx2']
      have h22 : logb 2 a < 3 := by 
        nlinarith [hx1', hx2']
      have ha1 : 4 < a := by
        have h31 : 2 < logb 2 a := h21 
        have h41 : logb 2 a > (2 : ℝ) := h31
        have h44 : logb 2 (4 : ℝ) = (2 : ℝ) := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
        have h45 : logb 2 a > logb 2 (4 : ℝ) := by
          linarith [h41, h44]
        have h46 : (0 : ℝ) < (4 : ℝ) := by linarith
        have h47 : (0 : ℝ) < (a : ℝ) := by linarith [ha.1]
        have h48 : (0 : ℝ) < (2 : ℝ) := by norm_num 
        have h49 : logb 2 a > logb 2 (4 : ℝ) := h45 
        have h50 : (4 : ℝ) < (a : ℝ) := by 
          apply (logb_lt_logb_iff (by linarith) (by linarith) (by nlinarith)).mp at h49 
          linarith 
        linarith 
      have ha2 : a < 8 := by
        have h32 : logb 2 a < (3 : ℝ) := h22 
        have h54 : logb 2 (8 : ℝ) = (3 : ℝ) := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
        have h55 : logb 2 a < logb 2 (8 : ℝ) := by 
          linarith [h32, h54]
        have h56 : (0 : ℝ) < (8 : ℝ) := by norm_num 
        have h57 : (0 : ℝ) < (a : ℝ) := by linarith [ha.1]
        have h58 : (0 : ℝ) < (2 : ℝ) := by norm_num 
        have h59 : logb 2 a < logb 2 (8 : ℝ) := h55 
        have h60 : a < (8 : ℝ) := by 
          apply (logb_lt_logb_iff ( by linarith) (by linarith) (by nlinarith)).mp at h59 
          linarith 
        linarith 
      constructor
      · exact ha1 
      · exact ha2
  · -- Case x1 = 3 * logb 2 a 
    have hx1' : x1 = 3 * logb 2 a := by linarith
    cases' (mul_eq_zero.mp h2) with h5 h6
    · -- Case x2 = logb 2 a 
      have hx2' : x2 = logb 2 a := by linarith
      nlinarith 
    · -- Case x2 = 3 * logb 2 a 
      have hx2' : x2 = 3 * logb 2 a := by linarith 
      nlinarith [hx1', hx2']