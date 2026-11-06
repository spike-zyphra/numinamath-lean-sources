import Mathlib

/- Suppose that a and b are nonzero real numbers, and that the equation 
x²+ax+b=0 has solutions a and b. Then the pair (a,b) is 
(A) (−2,1)
(B) (−1,2)
(C) (1,−2)
(D) (2,−1)
(E) (4,4) -/
theorem algebra_94250 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) 
(h : ∃ x y, x = a ∧ y = b ∧ x^2 + a * x + b = 0 ∧ y^2 + a * y + b = 0) :
a = 1 ∧ b = -2 := by
  --obtain a and b and put them in the equation instead of x and y
  obtain ⟨x, y, hxa, hyb, haa, hbb⟩ := h
  rw[hxa] at haa
  rw[hyb] at hbb
  --substitute b=-2a² in the second equation and obtain an expression in terms of a
  have hha : b = -2 * a ^ 2 := by ring_nf at haa; linarith
  rw[hha] at hbb
  have ka : (-2 * a ^ 2) ^ 2 + a * (-2 * a ^ 2) + -2 * a ^ 2 = 2 * a ^ 2 * (2 * a ^ 2 - a - 1) := by ring_nf
  rw[ka] at hbb
  --this expression factors as p(a)*q(a)=0 hence either p(a)=0 or q(a)=0
  have kaz : 2 * a ^ 2 = 0 ∨ 2 * a ^ 2 - a - 1 = 0 := by rw[mul_eq_zero] at hbb; exact hbb
  obtain h1|h2 := kaz
  --case 2a² = 0 is a contradiction 
  · have u : (2:ℝ) = 0 ∨ a ^ 2 = 0 := by rw[mul_eq_zero] at h1; exact h1
    obtain u1|u2:=u
    --we get 2=0
    · have c: 1 = 0 := by linarith
      contradiction
    --or a=0
    · have u2' : a ^ 2 = a * a := by linarith
      rw[u2'] at u2
      have v : a = 0 ∨ a = 0 := by rw[mul_eq_zero] at u2; exact u2
      obtain v1|v2:=v
      · contradiction
      · contradiction
  --case 2a²-a-1=0 
  · have j: 2 * a ^ 2 - a - 1 = (2 * a + 1) * (a - 1) := by ring_nf
    rw[j] at h2
    have kz : 2 * a + 1 = 0 ∨ a - 1 = 0 := by rw[mul_eq_zero] at h2; exact h2
    obtain j1|j2 := kz
    --case 2a+1 = 0 is a contradiction 
    · have jj : a = - 1 / 2 := by linarith
      rw[jj] at haa
      ring_nf at haa
      have kk : b = - 1 / 2 := by linarith
      rw[jj, kk] at hab
      contradiction
    --case a-1=0 
    · have s1 : a = 1 := by linarith
      rw[s1] at haa
      ring_nf at haa
      have s2 : b = -2 := by linarith
      constructor
      · exact s1
      · exact s2