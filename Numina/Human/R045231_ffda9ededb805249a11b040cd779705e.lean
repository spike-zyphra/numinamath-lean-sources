import Mathlib

/-
Let $a=\sqrt[1992]{1992}$. Which number is greater:

$$
\left.a^{a^{a^{a}}}\right\} 1992
$$

or 1992 ?
-/

theorem algebra_240739 (s : ℕ → ℝ) (hs1: s 1 = 1992^(1/1992)) (h: ∀ n, 1≤ n → s (n+1) = ((1992)^(1/(1992:ℝ)))^(s n)) : (s 1992) < 1992 := by

  -- we prove a stronger statement by induction: every tower of a is less than 1992.
  have prop : ∀ n, s (n+1) < 1992 := by 
    intro n
    induction' n with n hn


    -- for height 1, it's trivial
    have : 0 + 1 = 1 := by norm_num
    rw [this]; rw [hs1]; 
    have : (1992 :ℝ ) = (1992:ℝ )  ^ 1 := by norm_num
    nth_rw 2 [this]
    have : 1/ (1992:ℝ) < 1 :=  by norm_num
    refine pow_lt_pow_right₀ ?_ ?_; norm_num; norm_num


    -- for height n+1, assuming smaller towers are all less, show that next one is also less. 
    -- It follows from a fact that 1992^x < 1992 iff x<1.
    have hind : s (n+1+1) = ((1992)^(1/(1992:ℝ)))^(s (n+1)) := by apply h; linarith
    rw [← Real.rpow_mul] at hind
    rw [hind]
    have : (1992 :ℝ ) = (1992:ℝ )  ^ (1:ℝ) := by norm_num
    nth_rw 3 [this]
    have tmp1: (1 / 1992 * s (n + 1)) < 1 := by 
      field_simp [hn]; nlinarith
    have tmp2: 1 < (1992:ℝ) := by norm_num
    apply Real.rpow_lt_rpow_of_exponent_lt tmp2 tmp1
    linarith 


  have : s (1991+1) < 1992 := by apply prop
  have : 1992 = 1991 + 1 := by norm_num
  rw [this]; assumption