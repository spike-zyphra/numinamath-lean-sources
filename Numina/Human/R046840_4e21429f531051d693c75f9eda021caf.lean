import Mathlib

/- 3. Prove that for every $n \geq 3$ there exist odd numbers $x$ and $y$ such that $2^{n}=7 x^{2}+y^{2}$. -/
theorem number_theory_227925 (n : ℕ) (hn : 3 ≤ n) :
    ∃ x y : ℤ, Odd x ∧ Odd y ∧ 2^n = 7 * x^2 + y^2 := by



  -- We prove it by induction
  have lem : ∀ m:ℕ, ∃ x y : ℤ,  Odd x ∧ Odd y ∧ 2^(m+3) = 7 * x^2 + y^2 := by
    intro m 
    induction' m with m hm
    use 1,1; simp

    -- Suppse we have the claim for n = m+3.
    obtain ⟨x,y,xodd,yodd, hxy⟩ := hm
    have xpy2d: Even (x + y) := by exact Odd.add_odd xodd yodd
    have xmy2d: Even (x - y) := by exact Odd.sub_odd xodd yodd
    have sxmy: Even (7*x - y) := by 
      have : Odd (7:ℤ) := by use 3; norm_num
      have : Odd (7*x) := by refine Int.odd_mul.mpr ?_; tauto
      exact Odd.sub_odd this yodd
    have sxpy: Even (7*x + y) := by 
      have : Odd (7:ℤ) := by use 3; norm_num
      have : Odd (7*x) := by refine Int.odd_mul.mpr ?_; tauto
      exact Odd.add_odd this yodd
    obtain ⟨s,hs⟩ := xpy2d
    obtain ⟨t,ht⟩ := sxmy
    obtain ⟨u,hu⟩ := xmy2d
    obtain ⟨v,hv⟩ := sxpy
    -- We rewrite the equation for n = m +3 + 1
    have eq1 : (2)^(m+1+3) = 7 * s^2 + t^2 := by 
      rw [pow_succ]
      rw [hxy]
      have eq: (7 * (x:ℝ) ^ 2 + (y:ℝ) ^ 2) * 2 = 7 * (((x:ℝ) + (y:ℝ)) / 2) ^ 2 + ((7 * (x:ℝ) - (y:ℝ)) / 2) ^ 2 := by field_simp; ring_nf
      
      have : s = (((x:ℝ) + (y:ℝ)) / 2) := by 
        field_simp; ring_nf at hs ⊢; rify at hs; 
        rw [← hs]
      rw [←this] at eq
      
      have : t = ((7*x:ℝ)-y)/2 := by
        field_simp; ring_nf at ht ⊢; rify at ht;
        rw [← ht]
      rw [←this] at eq
      norm_cast at eq

    have eq2 : (2)^(m+1+3) = 7 * u^2 + v^2 := by 
      rw [pow_succ]
      rw [hxy]
      have eq: (7 * (x:ℝ) ^ 2 + (y:ℝ) ^ 2) * 2 = 7 * (((x:ℝ) - (y:ℝ)) / 2) ^ 2 + ((7 * (x:ℝ) + (y:ℝ)) / 2) ^ 2 := by field_simp; ring_nf

      have : u = ((x-y):ℝ)/2 := by
        field_simp; ring_nf at hu ⊢; rify at hu;
        rw [← hu]
      rw [←this] at eq

      have : v = ((7*x:ℝ)+y)/2 := by
        field_simp; ring_nf at hv ⊢; rify at hv;
        rw [← hv]
      rw [←this] at eq
      norm_cast at eq
    
    --We have s and t are both odd, or u and v are both odd.
    have cla : (Odd s ∧ Odd t) ∨ (Odd u ∧ Odd v) := by 
      by_cases os: Odd s
      left
      have ot : Odd t := by 
        have teq: t = 4 * x + (-s) := by linarith
        have ev4x: Even (4*x) := by use 2*x; linarith
        have oms: Odd (-s) := by exact Odd.neg os
        rw [teq]; exact Even.add_odd ev4x oms
      tauto

      right;
      have es: Even s := by exact Int.not_odd_iff_even.mp os
      have ou : Odd u := by 
        have ueq: u = s + (- y) := by linarith
        have : Odd (-y) := by exact Odd.neg yodd
        rw [ueq]; exact Even.add_odd es this
      have ov : Odd v := by 
        have et: Even t := by
          have teq: t = 4 * x + (-s) := by linarith
          have ev4x: Even (4*x) := by use 2*x; linarith
          have ems: Even (-s) := by exact Even.neg es
          rw [teq]; exact Even.add ev4x ems
        have veq: v = y + t := by linarith
        rw [veq]; exact Even.odd_add et yodd
      tauto

    rcases cla with claa | clab
    use s, t; tauto
    use u, v; tauto    


  
  have : ∃ k : ℕ, k + 3 = n := by use n-3; omega
  obtain ⟨k,hk⟩ := this
  have : ∃ x y :ℤ, Odd x ∧ Odd y ∧ 2 ^ (k + 3) = 7 * x ^ 2 + y ^ 2 := by apply lem k
  rw [hk] at this; simp_all; 
