import Mathlib

/- Given $a, b, c>0$ such that: $a+b+c=1$. Prove that:

$$
\frac{a}{b}+\frac{a}{c}+\frac{b}{a}+\frac{b}{c}+\frac{c}{a}+\frac{c}{b}+6 \geqslant 2 \sqrt{2}\left(\sqrt{\frac{1-a}{a}}+\sqrt{\frac{1-c}{c}}+\sqrt{\frac{1-b}{b}}\right)
$$

and determine when equality holds. -/
theorem algebra_607253 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) :
  a / b + a / c + b / a + b / c + c / a + c / b + 6 ≥ 2 * √2 * (√((1 - a) / a) + √((1 - c) / c) + √((1 - b) / b)) ∧ (a / b + a / c + b / a + b / c + c / a + c / b + 6 = 2 * √2 * (√((1 - a) / a) + √((1 - c) / c) + √((1 - b) / b)) ↔ a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3):= by
    -- Rewrite 1-a, 1-b, 1-c using the sum condition
    rw [show 1 - a = b + c by linarith]
    rw [show 1 - b = a + c by linarith]
    rw [show 1 - c = a + b by linarith]

    -- Key lemma: For any positive x, 2√2√x ≤ 2 + x with equality iff x = 2
    have h1 : ∀ x : ℝ, x > 0 → 2 * √2 * √x ≤ 2 + x ∧ (2 * √2 * √x = 2 + x → x = 2):= by
      intro x hx
      -- Proof using (√x - √2)² ≥ 0
      have h1 : (√x - √2) ^ 2 ≥ 0:= by positivity
      ring_nf at h1
      rw [show √x ^ 2 = x by refine Real.sq_sqrt (by positivity)] at h1
      rw [show √2 ^ 2 = 2 by norm_num] at h1
      constructor
      .
        linarith
      .
        intro h
        replace h1 : (√x - √2) ^ 2 = 0:= by
          ring_nf
          norm_num
          rw [show √x ^ 2 = x by refine Real.sq_sqrt (by positivity)]
          linarith
        replace h1 : √x - √2 = 0:= by exact pow_eq_zero h1
        replace h1 : √x = √2:= by linarith
        rw [show x = √x ^ 2 by refine Eq.symm (Real.sq_sqrt (by positivity))]
        rw [h1]
        norm_num

    -- Apply the lemma to our three terms
    have h2:= h1 ((b + c) / a) (by positivity)
    have h3:= h1 ((a + b) / c) (by positivity)
    have h4:= h1 ((a + c) / b) (by positivity)
    rcases h2 with ⟨h2, h2eq⟩
    rcases h3 with ⟨h3, h3eq⟩
    rcases h4 with ⟨h4, h4eq⟩
    constructor
    .
      -- Prove the inequality by combining the three inequalities
      rw [show 2 + (b + c) / a = 2 + b / a + c / a by field_simp; linarith] at h2
      rw [show 2 + (a + b) / c = 2 + a / c + b / c by field_simp; linarith] at h3
      rw [show 2 + (a + c) / b = 2 + a / b + c / b by field_simp; linarith] at h4
      linarith
    .
      constructor
      .
        -- Prove equality case implies a = b = c = 1/3
        intro hgoal
        have h5 : (b + c) / a = b / a + c / a:= by field_simp
        have h6 : (a + b) / c = a / c + b / c:= by field_simp
        have h7 : (a + c) / b = a / b + c / b:= by field_simp
        rw [show a / b + a / c + b / a + b / c + c / a + c / b = (b + c) / a + (a + b) / c + (a + c) / b by linarith] at hgoal
        have g1 : 2 * √2 * √((b + c) / a) = 2 + (b + c) / a:= by linarith
        have g2 : 2 * √2 * √((a + b) / c) = 2 + (a + b) / c:= by linarith
        have g3 : 2 * √2 * √((a + c) / b) = 2 + (a + c) / b:= by linarith
        replace h2eq:= h2eq g1
        replace h3eq:= h3eq g2
        replace h4eq:= h4eq g3
        rw [show b + c = 1 - a by linarith] at h2eq
        rw [show a + b = 1 - c by linarith] at h3eq
        rw [show a + c = 1 - b by linarith] at h4eq
        field_simp at h2eq h3eq h4eq
        refine ⟨(by linarith), (by linarith), (by linarith)⟩
      .
        -- Verify that a = b = c = 1/3 gives equality
        intro ⟨g1, g2, g3⟩
        subst a b c
        norm_num
        ring_nf
        norm_num
