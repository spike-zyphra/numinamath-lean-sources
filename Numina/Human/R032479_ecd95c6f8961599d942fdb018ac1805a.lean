import Mathlib

/- 28. [15] Let $x$ be a complex number such that $x+x^{-1}$ is a root of the polynomial $p(t)=t^{3}+t^{2}-2 t-1$. Find all possible values of $x^{7}+x^{-7}$. -/

theorem algebra_164592 {x : ℂ} (hx : x ≠ 0) (h : (x + 1/x)^3 + (x + 1/x)^2 - 2*(x + 1/x) - 1 = 0) :
    x^7 + 1/x^7 = 2 := by

    --The given assumption gives 1/x^3 * (1+x+x^2+x^3+x^4+x^5+x^6), so (1+x+x^2+x^3+x^4+x^5+x^6) = 0
    have : (x + 1/x)^3 + (x + 1/x)^2 - 2*(x + 1/x) - 1 = 1/x^3 * (1+x+x^2+x^3+x^4+x^5+x^6) := by field_simp; ring_nf
    rw [this] at h
    have xppeq0: (1+x+x^2+x^3+x^4+x^5+x^6) = 0 := by
      have : 1/x^3 ≠ 0 := by simp [hx]
      exact (mul_eq_zero_iff_left this).mp h

    --Easily we have x≠1, so now x^7 - 1 = 0 and hence x^7=1.
    have : x-1≠0 := by
        by_contra xm1eq0
        have xeq1 : x=1 := by 
          have : x - 1 + 1 = 0 + 1 := by exact congrFun (congrArg HAdd.hAdd xm1eq0) 1
          ring_nf at this; assumption
        rw [xeq1] at h; norm_num at h

    have : (x^7-1) / (x-1) = (1+x+x^2+x^3+x^4+x^5+x^6) := by      
      field_simp; ring_nf

    rw [←this] at xppeq0
    have x7eq : x^7 = 1 := by 
      have : x^7 - 1 = 0 := by simp at xppeq0; tauto
      have : x^7 - 1 + 1 = 0 + 1 := by exact congrFun (congrArg HAdd.hAdd this) 1
      ring_nf at this; assumption
    rw [x7eq]; ring_nf