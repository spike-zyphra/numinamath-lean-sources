import Mathlib

/- 10.4. The sequences $\left\{a_{n}\right\}$ and $\left\{b_{n}\right\}$ satisfy $a_{1}=1, b_{1}=$ $2, a_{n+1}=\frac{1+a_{n}+a_{n} b_{n}}{b_{n}}, b_{n+1}=\frac{1+b_{n}+a_{n} b_{n}}{a_{n}}$. Prove: $a_{2008}<5$. -/
theorem algebra_303930 (a b : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : b 1 = 2)
    (h₂ : ∀ n, a (n + 1) = (1 + a n + a n * b n) / b n)
    (h₃ : ∀ n, b (n + 1) = (1 + b n + a n * b n) / a n) :
    a 2008 < 5 := by

    -- We prove by induction that for every m ≥ 1, we have 1/ (a_m + 1) = 1/ (b_m +1) + 1/6, so a_m<5.
    have lem : ∀ m : ℕ, 0<a (m+1) ∧ 0 < b (m+1) ∧ 1/(a (m+1) + 1) - 1/(b (m+1) + 1) = 1/6 := by
      intro m
      induction' m with k hk
      simp_all; ring_nf

      have akp1pos: 0 < a (k+1) := by exact hk.left
      have bkp1pos: 0 < b (k+1) := by exact hk.right.left
      constructor
      rw [h₂]; 
      refine div_pos ?_ bkp1pos
      nlinarith
      constructor
      rw [h₃];
      refine div_pos ?_ akp1pos
      nlinarith

      have : 1 / (a (k + 1 + 1) + 1) - 1 / (b (k + 1 + 1) + 1) = 1 / (a (k + 1) + 1) - 1 / (b (k + 1) + 1)  := by 
        have t1: 1 / (a (k + 1 + 1) + 1) - 1 / (b (k + 1 + 1) + 1) = 1 / ((1 + a (k + 1) + a (k + 1) * b (k + 1)) / b (k + 1) + 1) - 1 /((1 + b (k + 1) + a (k + 1) * b (k + 1)) / a (k + 1) + 1) := by 
          have l1 : a (k + 1 + 1) = (1 + a (k + 1) + a (k + 1) * b (k + 1)) / b (k + 1) := by apply h₂ (k+1)
          have l2 : b (k + 1 + 1) = (1 + b (k + 1) + a (k + 1) * b (k + 1)) / a (k + 1) := by apply h₃ (k+1)
          rw [l1, l2]
        have t2: 1 / (a (k + 1) + 1) - 1 / (b (k + 1) + 1) = (b (k+1) - a (k+1)) / ((1 + a (k+1))*(1+ b (k+1))) := by field_simp; ring_nf; left; trivial
        rw [t1,t2]
        field_simp; ring_nf
      linarith
    
    -- just apply the induction hypothesis to 2007
    have cla : 0 < a (2007 + 1) ∧ 0 < b (2007 + 1) ∧ 1 / (a (2007 + 1) + 1) - 1 / (b (2007 + 1) + 1) = 1 / 6 := by apply lem 2007
    ring_nf at cla
    have : 1/6 < (1 + a 2008)⁻¹ := by 
      have : 0 < 1 + b 2008 := by linarith
      have : 0 < (1 + b 2008)⁻¹ := by exact inv_pos_of_pos this
      have : (1 + a 2008)⁻¹ = 1 / 6 + (1 + b 2008)⁻¹ := by linarith
      linarith
    have : 1 + a 2008 < 6 := by 
      by_contra g; push_neg at g
      have : 1/ (1 + a 2008) ≤ 1 / 6 := by refine one_div_le_one_div_of_le ?_ g; linarith
      ring_nf at this; linarith
    linarith