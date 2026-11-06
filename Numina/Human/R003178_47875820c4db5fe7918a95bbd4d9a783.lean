import Mathlib

open Real

-- 3. Let $a, b$, and $c$ be positive real numbers. Determine the largest total number of real roots that the following three polynomials may have among them: $a x^{2}+b x+c, b x^{2}+c x+a$, and $c x^{2}+a x+b$.
-- Answer: 4 If all the polynomials had real roots, their discriminants would all be nonnegative: $a^{2} \geq$ $4 b c, b^{2} \geq 4 c a$, and $c^{2} \geq 4 a b$. Multiplying these inequalities gives $(a b c)^{2} \geq 64(a b c)^{2}$, a contradiction. Hence one of the quadratics has no real roots. The maximum of 4 real roots is attainable: for example, the values $(a, b, c)=(1,5,6)$ give $-2,-3$ as roots to $x^{2}+5 x+6$ and $-1,-\frac{1}{5}$ as roots to $5 x^{2}+6 x+1$.


lemma encard_quadratic_zero (a b c : ℝ):
  a ≠ 0 →  b^2-4*a*c< 0 → {x : ℝ | a * x ^ 2 + b * x + c = 0}.encard = 0 := by
  intro ha h
  have : {x | a * x ^ 2 + b * x + c = 0} = ∅ := by
    ext x
    simp
    intro hx
    have : (b ^ 2 - 4 * a * c) = 4*(a*x+b/2)^2 := by
      rw [(by linarith : c= -a * x ^ 2 -b*x )]
      ring_nf

    have : 4*(a*x+b/2)^2 ≥ 0 := by positivity
    linarith

  rw [this]
  simp

lemma encard_quadratic_one (a b c : ℝ):
  a≠ 0 →  b^2-4*a*c = 0 → {x : ℝ | a * x ^ 2 + b * x + c = 0}.encard = 1 := by
  intro ha h
  have : {x : ℝ | a * x ^ 2 + b * x + c = 0} = {-(b/(2*a))} := by
    ext x
    simp
    constructor
    . intro hx
      have : a*(x+b/(2*a))^2 = (b ^ 2 - 4 * a * c)/(4*a) := by
        ring_nf
        field_simp
        rw [(by linarith : a * x ^ 2 = -b*x-c )]
        ring_nf

      rw [h] at this
      simp at this
      rcases this with h | h
      . contradiction
      . linarith
    . intro hx
      subst x
      ring_nf
      field_simp
      rw [(by linarith : b^2 = 4*a*c)]
      ring_nf

  rw [this]
  simp

lemma encard_quadratic_two (a b c : ℝ):
  a ≠ 0 →  b^2-4*a*c > 0 → {x : ℝ | a * x ^ 2 + b * x + c = 0}.encard = 2 := by
  intro ha h

  let x1 := -b/(2*a) - √(b^2-4*a*c)/(2*a)
  let x2 := -b/(2*a) + √(b^2-4*a*c)/(2*a)

  have hx12 : x1 ≠ x2 := by
    by_contra h
    unfold x1 x2 at h
    have : √(b^2-4*a*c)/(2*a) = 0 := by linarith
    simp at this
    rcases this with h | h
    . rw [sqrt_eq_zero (by linarith)] at h
      linarith
    . contradiction

  have hx1 : a * x1 ^ 2 + b * x1 + c = 0 := by
    unfold x1
    ring_nf
    rw [sq_sqrt (by linarith)]
    field_simp
    ring_nf

  have hx2 : a * x2 ^ 2 + b * x2 + c = 0 := by
    unfold x2
    ring_nf
    rw [sq_sqrt (by linarith)]
    field_simp
    ring_nf

  have : {x | a * x ^ 2 + b * x + c = 0} = {x1, x2} := by
    ext x
    simp
    constructor
    . intro hx
      have : a*(x-x1)*(x-x2) = 0 := by
        unfold x1 x2
        ring_nf
        field_simp
        rw [(by linarith : a * x ^ 2 = -b*x-c )]
        rw [sq_sqrt (by linarith)]
        ring_nf

      simp at this
      rcases this with h | h
      . rcases h with h | h
        . contradiction
        . left; linarith
      . right; linarith

    . intro hx
      rcases hx with hx | hx
      . subst x
        exact hx1
      . subst x
        exact hx2

  rw [this]
  rw [Set.encard_pair]
  exact hx12

lemma encard_quadratic_le_two (a b c : ℝ):
  a ≠ 0 → {x : ℝ | a * x ^ 2 + b * x + c = 0}.encard ≤ 2 := by
  intro ha
  rcases lt_trichotomy (b^2-4*a*c) 0 with h | h | h
  . have := encard_quadratic_zero a b c ha h
    rw [this]
    norm_num
  . have := encard_quadratic_one a b c ha h
    rw [this]
    norm_num
  . have := encard_quadratic_two a b c ha h
    rw [this]


theorem algebra_159472 :
  IsGreatest
    { n | ∃ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧
      n = {x : ℝ | a * x ^ 2 + b * x + c = 0}.encard
        + {x : ℝ | b * x ^ 2 + c * x + a = 0}.encard
        + {x : ℝ | c * x ^ 2 + a * x + b = 0}.encard }
    4 := by

  constructor
  . simp
    use 1
    norm_num
    use 5
    norm_num
    use 6
    constructor
    . norm_num
    . have := encard_quadratic_two 1 5 6 (by linarith) (by linarith)
      simp at this; rw [this]
      have := encard_quadratic_two 5 6 1 (by linarith) (by linarith)
      simp at this; rw [this]
      have := encard_quadratic_zero 6 1 5 (by linarith) (by linarith)
      simp at this; rw [this]
      norm_num

  . unfold upperBounds
    simp
    intro n a ha b hb c hc hn
    rw [hn]

    have : b^2 < 4*a*c ∨ c^2 < 4*a*b ∨ a^2 < 4*b*c := by
      by_contra h
      simp at h
      have ⟨ h1, h2, h3 ⟩ := h
      have := mul_le_mul h1 h2 (by positivity) (by positivity)
      have := mul_le_mul this h3 (by positivity) (by positivity)
      simp at this
      ring_nf at this
      have : a^2 * c^2 * b^2 > 0 := by positivity
      linarith


    rcases this with h | h | h
    . have := encard_quadratic_zero a b c (by linarith) (by linarith)
      rw [this]
      have h1:= encard_quadratic_le_two b c a (by linarith)
      have h2:= encard_quadratic_le_two c a b (by linarith)
      have h3:= add_le_add h1 h2
      norm_num at h3 ⊢
      exact h3
    . have := encard_quadratic_zero b c a (by linarith) (by linarith)
      rw [this, add_comm]
      have h1:= encard_quadratic_le_two c a b (by linarith)
      have h2:= encard_quadratic_le_two a b c (by linarith)
      have h3:= add_le_add h1 h2
      norm_num at h3 ⊢
      exact h3
    . have := encard_quadratic_zero c a b (by linarith) (by linarith)
      rw [this, add_comm]
      have h1:= encard_quadratic_le_two a b c (by linarith)
      have h2:= encard_quadratic_le_two b c a (by linarith)
      have h3:= add_le_add h1 h2
      norm_num at h3 ⊢
      exact h3
