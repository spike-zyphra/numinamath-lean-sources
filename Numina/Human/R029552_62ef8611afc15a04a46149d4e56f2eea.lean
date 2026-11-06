import Mathlib

/- Let $a,$ $b,$ $c,$ $d$ be distinct real numbers such that the roots of $x^2 - 10ax - 11b = 0$ are $c$ and $d,$ and the roots of $x^2 - 10cx - 11d = 0$ are $a$ and $b.$  Find the value of $a + b + c + d.$ -/
theorem algebra_13138 {a b c d : ℝ} (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : c^2 - 10*a*c - 11*b = 0) (h2 : d^2 - 10*a*d - 11*b = 0)
    (h3 : a^2 - 10*c*a - 11*d = 0) (h4 : b^2 - 10*c*b - 11*d = 0) :
    a + b + c + d = 1210 := by
  -- use Vieta's formula to find sum of two roots.
  -- x1+x2 = -b/a, and if we rewrite the equation in the form of x^2+b'x+c=0, then x1+x2 = b'.
  have vieta_lemma{bb cc x1 x2:ℝ} (hh1: x1^2-bb*x1+cc = 0) (hh2: x2^2-bb*x2+cc = 0) (hh3: x1 ≠ x2):  (x1 + x2 = bb) ∧ (x1*x2 = cc) := by
    rw [pow_two] at hh1 hh2
    have ht1 := vieta_formula_quadratic hh1
    have eq1: (x2-x1)*(x2-(bb-x1)) = 0 := by
      have tt1: (x2-x1)*(x2-(bb-x1)) = x2*x2-bb*x2+(bb-x1)*x1 := by ring
      have tt2: (bb-x1)*x1 = cc := by
        rcases ht1 with ⟨d,⟨eqd,dadd,dmul⟩⟩
        have hd: d = bb - x1 := by
          rw [← dadd];ring
        rw [← hd, mul_comm]; exact dmul
      rw [tt1,tt2]
      exact hh2
    have xeq': x2-x1 = 0 ∨ x2 - (bb-x1) = 0 := mul_eq_zero.mp eq1
    rcases xeq' with eq | ineq
    have: x2 = x1 := by
      rw [← add_zero x1, ← eq]; ring
    rw [this] at hh3; simp at hh3
    have hadd: x2 = bb-x1 := by
      rw [← add_zero (bb-x1), ← ineq]; ring
    have hmul: x1 * x2 = cc := by
      rcases ht1 with ⟨d,⟨eqd,dadd,dmul⟩⟩
      have: x1 = bb - x2 := by
        rw [hadd]; ring
      rw [this] at dadd
      have x2eq: d = x2 := by
        have: d = d+bb-bb := by ring
        rw [this]
        nth_rw 2 [← dadd];ring
      rw [← x2eq]
      exact dmul
    rw [hadd]; simp
    rw [← hadd]; exact hmul
  -- for equations of c and d, use vieta formula:
  have hcd := vieta_lemma h1 h2 hf
  -- equations of a and b, use vieta formula too.
  have hab := vieta_lemma h3 h4 ha
  --from c+d=10a, we have d = 10a-c
  have d_of_ac: d = 10*a-c := by
    have := hcd.left
    exact eq_sub_of_add_eq' this
  -- from a+b=10c, we get b = 10c-a
  have b_of_ac: b = 10*c-a := by
    have := hab.left
    exact eq_sub_of_add_eq' this
  -- substitute into other two equations.
  have hac1: c*(10*a-c) = -11*(10*c-a) := by
    rw [← b_of_ac, ← d_of_ac, hcd.right]; simp
  have hac2: a*(10*c-a) = -11*(10*a-c) := by
    rw [← b_of_ac, ← d_of_ac, hab.right]; simp
  -- expanding hac1 and hac2
  have hac1': 10*(a*c)-c^2 = -110*c+11*a := by
    have hleft: 10*(a*c)-c^2 = c*(10*a-c) := by ring
    rw [hleft, hac1]; ring
  have hac2': 10*(a*c)-a^2 = -110*a+11*c := by
    have hleft: 10*(a*c)-a^2 = a*(10*c-a) := by ring
    rw [hleft, hac2]; ring
  -- subtracting these equations.
  have hacsub: a^2-c^2 = 121*a-121*c := by
    have hleft: a^2-c^2 = (10*(a*c)-c^2)-(10*(a*c)-a^2) := by ring
    rw [hleft,hac1',hac2'];ring
  -- factorization
  have hacsub': (a+c)*(a-c) = 121*(a-c) := by
    have: (a+c)*(a-c) = a^2-c^2 := by ring
    rw [this, hacsub]; ring
  -- a-c ≠ 0, so we cancel it from both sides.
  have hacadd: a+c = 121 := by
    have ht1: a-c ≠ 0 := sub_ne_zero_of_ne hb
    have ht2: (a+c-121)*(a-c) = 0 := by
      rw [sub_mul, hacsub']; ring
    have ht3: a+c-121 = 0 ∨ a-c = 0 := mul_eq_zero.mp ht2
    rcases ht3 with h11 | h22
    linarith [h11]
    contradiction
  -- notice that b+d can be expressed in terms of a+c
  have hbdadd: b+d = 9*(a+c) := by
    rw [b_of_ac,d_of_ac]; ring
  -- therefore we can solve a+b+c+d
  have: a+b+c+d = (a+c) + (b+d) := by ring
  rw [this, hacadd, hbdadd, hacadd]
  ring