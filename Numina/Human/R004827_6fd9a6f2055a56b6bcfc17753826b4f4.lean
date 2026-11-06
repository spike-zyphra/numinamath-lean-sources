import Mathlib

open Real
/-
Theorem 1 If $a, b, c$ are the lengths of the three sides of $\triangle A B C$, then
$$\begin{array}{l}
\sqrt{a b-b c+b^{2}}+\sqrt{c a-b c+c^{2}}>\sqrt{a b+c a+a^{2}} \\
\sqrt{b c-c a+c^{2}}+\sqrt{a b-c a+a^{2}}>\sqrt{a b+b c+b^{2}} \\
\sqrt{c a-a b+a^{2}}+\sqrt{b c-a b+b^{2}}>\sqrt{b c+c a+c^{2}}
\end{array}$$
-/


--If suffices to prove the first one. The other two follows from symmetry.
lemma l1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1: c < a + b) (h2: b < a + c) (h3: a < b + c):
√(a*b+c*a+a^2) < √(a*b-b*c+b^2) + √(c*a-b*c+c^2) := by 
  
  --We use our assumption to get √(a^2- (b-c)^2) < √(4*b*c).
  have i0 : 0 < a^2 - (b-c)^2 := by 
    simp
    refine sq_lt_sq' ?_ ?_
    linarith
    linarith
  have i1 : a^2 - (b-c)^2 < 4 * b * c := by 
    ring_nf
    nlinarith
  have i2 : √(a^2- (b-c)^2) < √(4*b*c) := by
    rw [Real.sqrt_lt_sqrt_iff]
    exact i1 
    linarith

  --Now, mulitply both sides of the inequailty with √a^-(b-c)^2, we have the following inequality.
  have i3 : a^2 - (b-c)^2 < 2 * √((a^2- (b-c)^2)*b*c) := by 
    have e1 : a^2 - (b-c)^2 = √(a^2- (b-c)^2) * √(a^2- (b-c)^2) := by
      have : 0 ≤ (a^2- (b-c)^2) := by positivity
      exact Eq.symm (mul_self_sqrt this)
    have e2 : 2 * √((a^2- (b-c)^2)*b*c) = √((a^2- (b-c)^2)) * √(4*b*c) := by 
      have t1 : √(4*b*c) = 2 * √(b*c) := by
        refine sqrt_eq_cases.mpr ?_
        left
        ring_nf
        constructor
        field_simp
        ring_nf
        have : √b ^ 2 = b := by refine sq_sqrt ?_; linarith
        rw [this]
        have : √c ^ 2 = c := by refine sq_sqrt ?_; linarith
        rw [this]
        positivity
      rw [t1]
      have t2 : √(a ^ 2 - (b - c) ^ 2) * (2 * √(b * c)) = 2* √((a ^ 2 - (b - c) ^ 2) * (b*c)) := by 
        have : √(a ^ 2 - (b - c) ^ 2) * √(b * c) = √((a ^ 2 - (b - c) ^ 2) * (b*c)) := by 
          refine Eq.symm (sqrt_mul' (a ^ 2 - (b - c) ^ 2) ?_)
          positivity
        linarith
      rw [t2]
      ring_nf
    nth_rw 1 [e1]
    rw [e2]
    rw [mul_lt_mul_iff_of_pos_left]
    exact i2
    positivity


  have t1 : (√(a * b + c * a + a ^ 2))^2 = a*b+c*a + a^2 := by 
    refine sq_sqrt ?_
    positivity
  have t2 : (√(a * b - b * c + b ^ 2) + √(c * a - b * c + c ^ 2))^2 = a*b+c*a + (b-c)^2 + 2*√((a^2 - (b-c)^2)*b*c) := by 
    ring_nf
    have : √(a * b - b * c + b ^ 2) ^ 2 = a * b - b * c + b ^ 2 := by 
      refine sq_sqrt ?_
      nlinarith
    rw [this]
    have : √(a * c - b * c + c ^ 2) ^ 2 = (a * c - b * c + c ^ 2) := by 
      refine sq_sqrt ?_
      nlinarith
    rw [this]
    ring_nf
    have : √(a * b - b * c + b ^ 2) * √(a * c - b * c + c ^ 2) = √(a ^ 2 * b * c - b * c ^ 3 + (b ^ 2 * c ^ 2 * 2 - b ^ 3 * c)) := by 
      have : √(a * b - b * c + b ^ 2) * √(a * c - b * c + c ^ 2) = √((a * b - b * c + b ^ 2) * ((a * c - b * c + c ^ 2))) := by 
        refine Eq.symm (sqrt_mul' (a * b - b * c + b ^ 2) ?_)
        nlinarith
      rw [this]
      ring_nf
    rw [this]
  --Take the square of both sides, and i3 is just what we need.
  have i4 : (√(a * b + c * a + a ^ 2))^2 < (√(a * b - b * c + b ^ 2) + √(c * a - b * c + c ^ 2))^2 := by
    rw [t1,t2]
    linarith
    
  rw [sq_lt_sq₀] at i4
  exact i4
  positivity
  positivity

theorem inequalities_600668 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1: c < a + b) (h2: b < a + c) (h3: a < b + c):
  √(a*b-b*c+b^2) + √(c*a-b*c+c^2) > √(a*b+c*a+a^2) ∧
  √(b*c-c*a+c^2) + √(a*b-c*a+a^2) > √(a*b+b*c+b^2) ∧
  √(c*a-a*b+a^2) + √(b*c-a*b+b^2) > √(b*c+c*a+c^2) := by
  
  simp
  
  constructor
  exact l1 a b c ha hb hc h1 h2 h3
  
  constructor
  rw [add_comm] at h1 h2
  have t := by exact l1 b c a hb hc ha h3 h1 h2
  nth_rw 2 [add_comm]
  exact t

  rw [add_comm] at h2 h3
  have t := by exact l1 c a b hc ha hb h2 h3 h1
  nth_rw 2 [add_comm]
  exact t