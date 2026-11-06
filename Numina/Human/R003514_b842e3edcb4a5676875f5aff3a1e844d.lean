import Mathlib

/- \section*{Problem 6 - 241036}

Determine for each function \(f\) that satisfies the following properties (1), (2), and (3), the function values \(f(0), f(-1)\), and \(f\left(\frac{3}{7}\right)\).

(1) The function \(f\) is defined for all real numbers.

(2) It holds that \(f(1)=2\).

(3) For all real numbers \(a\) and \(b\), it holds that \(f(a+b)=f(a) \cdot f(b)\). -/
theorem algebra_189724 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y) (h1 : f 1 = 2) :
    f 0 = 1 ∧ f (-1) = 1 / 2 ∧ f (3 / 7) = 2 ^ (3 / (7:ℝ)) := by

    -- 1. Calculate f(0) by using f 1.
    have t1: f (1+0) = f 1 * f 0 := by apply h 1 0
    ring_nf at t1; simp [h1] at t1

    -- 2. Calculate f -1 by using f 1 and f 0.
    have tm1 : f (1 + (-1)) = f 1 * f (-1) := by apply h 1 (-1)
    ring_nf  at tm1; simp [h1, t1] at tm1;
    have : f (-1) = 1/2 := by nlinarith

    -- For the last quantity, we have the following lemma: f (nx) = (fx)^n. Then, we can easily get f (3/7).
    have lem : ∀n : ℕ, ∀ x : ℝ,  f (n * x) =  (f x)^n := by
      intro n
      induction' n with n hn
      simp; assumption
      intro x
      have r1 : ↑(n + 1) * x = n * x + x := by push_cast; ring_nf
      rw [r1]
      have r2 : f (↑n * x + x)  = f (↑n * x) * f x := by apply h (↑n * x) x
      rw [r2]; rw [hn]; ring_nf
    have tmp2 : f (3) = (f 1)^3 := by
      have : f (↑3 * 1) = f 1 ^ 3 := by apply lem 3 1
      ring_nf at this; assumption
    rw [h1] at tmp2;
    have tmp3 : f 3 = (f (3/7))^7 := by
      have : f (↑7 * (3 / 7)) = f (3 / 7) ^ 7 := by apply lem 7 (3/7)
      ring_nf at this; assumption
    have f37pos : 0 ≤  (f (3/7)) := by
      by_contra ifneg; push_neg at ifneg
      have : Odd 7 := by use 3; norm_num
      have : f (3 / 7) ^ 7 < 0 := by exact Odd.pow_neg this ifneg
      linarith
    rw [tmp3] at tmp2
    have  : f (3 / 7) = 2^(3/(7:ℝ)) := by
      have eq1: (f (3 / 7) ^ 7)^(1/(7:ℝ)) = (2 ^ 3)^(1/(7:ℝ)) := by rw [tmp2]
      have d1 : (f (3 / 7) ^ 7)^(1/(7:ℝ)) = (f (3 / 7) ^ (7*(1/(7:ℝ)))) := by field_simp; ring_nf; rw [←Real.rpow_natCast_mul f37pos 7 (1 / 7)]; norm_num
      rw [d1] at eq1;
      have : ((2:ℝ) ^ 3) ^ ( (1:ℝ) / (7:ℝ)) = (2:ℝ) ^ ((3:ℝ)/(7:ℝ) ) := by
        have : 3 / (7:ℝ) = (3:ℝ)*(1/(7:ℝ)) := by ring_nf
        rw [this]
        have : 0 ≤ (2:ℝ) := by norm_num
        rw [← Real.rpow_natCast_mul this]
        norm_num
      rw [this] at eq1; norm_num at eq1
      exact eq1
      
    tauto
