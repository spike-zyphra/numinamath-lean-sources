import Mathlib
/- 1. Given real numbers $a$, $b$, $c$ satisfy $(a+b)(b+c)(c+a)=0$ and $abc<0$. Then the value of the algebraic expression $\frac{a}{|a|}+\frac{b}{|b|}+\frac{c}{|c|}$ is -/
theorem algebra_304626 {a b c : ℝ} (h1 : (a + b) * (b + c) * (c + a) = 0) (h2 : a * b * c < 0) :
a / |a| + b / |b| + c / |c| = 1:= by
  -- Lemma: If x + y = 0 and both x and y are non-zero, then x*y < 0
  have h3 : ∀ x y : ℝ, x + y = 0 → x ≠ 0 → y ≠ 0 → x * y < 0:= by
    intro x y h3 h4 h5
    replace h3 : x = -y:= by linarith
    subst x
    ring_nf
    suffices y ^ 2 > 0 by linarith
    positivity

  -- Lemma: If x + y = 0 and both x and y are non-zero, then x/|x| + y/|y| = 0
  have h4 : ∀ x y : ℝ, x + y = 0 → x ≠ 0 → y ≠ 0 → x / |x| + y / |y| = 0:= by
    intro x y h4 _ h6
    have h7 : x = -y:= by linarith
    replace h7 : |x| = |-y|:= by rw [h7]
    simp at h7
    rw [h7]
    field_simp
    exact h4

  -- Simplify the first hypothesis
  simp at h1

  -- Establish that a, b, and c are all non-zero
  have g : a * b * c ≠ 0:= by linarith
  simp at g
  rcases g with ⟨⟨g1, g2⟩, g3⟩

  -- Split into three cases based on which factor equals zero: (a+b), (b+c), or (c+a)
  rcases h1 with ⟨h1 | h1⟩ | h1

  -- Case 1: a + b = 0
  .
    specialize h3 a b h1 g1 g2
    specialize h4 a b h1 g1 g2
    -- Prove that c > 0 using the fact that a*b*c < 0 and a*b < 0
    replace h2 : c > 0:= by exact (neg_iff_pos_of_mul_neg h2).mp h3
    -- Simplify |c| to c since c > 0
    rw [show |c| = c by exact abs_of_pos h2]
    -- Use the lemma to simplify a/|a| + b/|b| to 0
    rw [h4]
    field_simp

  -- Case 2: b + c = 0
  .
    specialize h3 b c h1 g2 g3
    specialize h4 b c h1 g2 g3
    -- Rearrange a*b*c to a*(b*c) to use with the lemma
    rw [show a * b * c = a * (b * c) by ring] at h2
    -- Prove that a > 0 using the fact that a*b*c < 0 and b*c < 0
    replace h2 : a > 0:= by exact (pos_iff_neg_of_mul_neg h2).mpr h3
    -- Simplify |a| to a since a > 0
    rw [show |a| = a by exact abs_of_pos h2]
    -- Simplify a/a to 1
    rw [show a / a = 1 by field_simp]
    linarith

  -- Case 3: c + a = 0
  .
    specialize h3 c a h1 g3 g1
    specialize h4 c a h1 g3 g1
    -- Rearrange a*b*c to b*(c*a) to use with the lemma
    rw [show a * b * c = b * (c * a) by ring] at h2
    -- Prove that b > 0 using the fact that a*b*c < 0 and c*a < 0
    replace h2 : b > 0:= by exact (pos_iff_neg_of_mul_neg h2).mpr h3
    -- Simplify |b| to b since b > 0
    rw [show |b| = b by exact abs_of_pos h2]
    -- Simplify b/b to 1
    rw [show b / b = 1 by field_simp]
    linarith
