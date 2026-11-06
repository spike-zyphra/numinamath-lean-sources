import Mathlib
open Real

/-
Let $f(x)=x^{2}-2 x$. How many distinct real numbers $c$ satisfy $f(f(f(f(c))))=3$ ?
-/
def f (x : ℝ) := x ^ 2 - 2 * x

theorem algebra_611485 (c:ℝ) (hf: f (f (f (f c))) = 3) : ((c = 1)∨(c = -1)∨(c = 3)∨(c = 1)∨(c = 1 + sqrt 2)∨(c = 1-sqrt 2)∨(c = 1-sqrt 2)∨
(c = 1 + sqrt (2 + sqrt 2)) ∨ (c = 1 - sqrt (2 + sqrt 2)) ∨
(c = 1 + sqrt (2 - sqrt 2)) ∨ (c = 1 - sqrt (2 - sqrt 2))) := by

  have h1 : f (f (f c)) ^ 2 - 2 * f (f (f c)) = 3 := by
    simp [f] at hf ⊢
    linarith

  have h2 : (f (f (f c)) - 3) * (f (f (f c)) + 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where $f(f(f c)) = 3$
    have h5 : f (f (f c)) = 3 := by linarith
    have h6 : f (f c) ^ 2 - 2 * f (f c) = 3 := by
      simp [f] at h5 ⊢
      nlinarith
    have h7 : (f (f c) - 3) * (f (f c) + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case where $f(f c) = 3$
      have h10 : f (f c) = 3 := by linarith
      have h11 : f c ^ 2 - 2 * f c = 3 := by
        simp [f] at h10 ⊢
        nlinarith
      have h12 : (f c - 3) * (f c + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h12) with h13 h14
      · -- Case where $f c = 3$
        have h15 : f c = 3 := by linarith
        have h16 : c^2 - 2 * c = 3 := by
          simp [f] at h15 ⊢
          nlinarith
        have h17 : (c - 3) * (c + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h17) with h18 h19
        · -- Case $c = 3$
          have hc : c = 3 := by linarith
          simp [hc]
        · -- Case $c = -1$
          have hc : c = -1 := by linarith
          simp [hc]
      · -- Case where $f c = -1$
        have h20 : f c = -1 := by linarith
        have h21 : c^2 - 2 * c = -1 := by
          simp [f] at h20 ⊢
          nlinarith
        have h22 : (c - 1) ^ 2 = 0 := by
          nlinarith
        have hc : c = 1 := by
          nlinarith
        simp [hc]
    · -- Case where $f(f c) = -1$
      have h23 : f (f c) = -1 := by linarith
      have h24 : f c ^ 2 - 2 * f c = -1 := by
        simp [f] at h23 ⊢
        nlinarith
      have h25 : (f c - 1) ^ 2 = 0 := by
        nlinarith
      have h26 : f c = 1 := by
        nlinarith
      have h27 : c^2 - 2 * c = 1 := by
        simp [f] at h26 ⊢
        nlinarith
      have h28 : c^2 - 2 * c - 1 = 0 := by
        linarith
      have h29 : (c - (1 + Real.sqrt 2)) * (c - (1 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
      cases' (mul_eq_zero.mp h29) with h30 h31
      · -- Case $c = 1 + \sqrt{2}$
        have hc : c = 1 + Real.sqrt 2 := by linarith
        simp [hc]
      · -- Case $c = 1 - \sqrt{2}$
        have hc : c = 1 - Real.sqrt 2 := by linarith
        simp [hc]
  · -- Case where $f(f(f c)) = -1$
    have h32 : f (f (f c)) = -1 := by linarith
    have h33 : f (f c) ^ 2 - 2 * f (f c) = -1 := by
      simp [f] at h32 ⊢
      nlinarith
    have h34 : (f (f c) - 1) ^ 2 = 0 := by
      nlinarith
    have h35 : f (f c) = 1 := by
      nlinarith
    have h36 : f c ^ 2 - 2 * f c = 1 := by
      simp [f] at h35 ⊢
      nlinarith
    have h37 : f c ^ 2 - 2 * f c - 1 = 0 := by
      linarith
    have h38 : (f c - (1 + Real.sqrt 2)) * (f c - (1 - Real.sqrt 2)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
    cases' (mul_eq_zero.mp h38) with h39 h40
    · -- Case where $f c = 1 + \sqrt{2}$
      have h41 : f c = 1 + Real.sqrt 2 := by linarith
      have h42 : c^2 - 2 * c = 1 + Real.sqrt 2 := by
        simp [f] at h41 ⊢
        nlinarith
      have h43 : c^2 - 2 * c - (1 + Real.sqrt 2) = 0 := by
        linarith
      have h44 : (c - (1 + Real.sqrt (2 + Real.sqrt 2))) * (c - (1 - Real.sqrt (2 + Real.sqrt 2))) = 0 := by
        nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + Real.sqrt 2) by positivity), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h44) with h45 h46
      · -- Case $c = 1 + \sqrt{2 + \sqrt{2}}$
        have hc : c = 1 + Real.sqrt (2 + Real.sqrt 2) := by linarith
        simp [hc]
      · -- Case $c = 1 - \sqrt{2 + \sqrt{2}}$
        have hc : c = 1 - Real.sqrt (2 + Real.sqrt 2) := by linarith
        simp [hc]
    · -- Case where $f c = 1 - \sqrt{2}$
      have h47 : f c = 1 - Real.sqrt 2 := by linarith
      have h48 : c^2 - 2 * c = 1 - Real.sqrt 2 := by
        simp [f] at h47 ⊢
        nlinarith
      have h49 : c^2 - 2 * c - (1 - Real.sqrt 2) = 0 := by
        linarith
      have h50 : (c - (1 + Real.sqrt (2 - Real.sqrt 2))) * (c - (1 - Real.sqrt (2 - Real.sqrt 2))) = 0 := by
        nlinarith [Real.sqrt_nonneg (2 - Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 - Real.sqrt 2) by 
          have h51 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          nlinarith [Real.sqrt_nonneg 2]
        ), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h50) with h52 h53
      · -- Case $c = 1 + \sqrt{2 - \sqrt{2}}$
        have hc : c = 1 + Real.sqrt (2 - Real.sqrt 2) := by linarith
        simp [hc]
      · -- Case $c = 1 - \sqrt{2 - \sqrt{2}}$
        have hc : c = 1 - Real.sqrt (2 - Real.sqrt 2) := by linarith
        simp [hc]