import Mathlib
/- Example 23 (Recorded from "China Inequality Research Group Website", hljhdf, 2007.09.08 provided) Let $a$, $b, c \in \mathbf{R}^{+}$, then
$$\sum \frac{a^{3}}{b^{2}-b c+c^{2}} \geqslant \sum a$$

Equality in (29) holds if and only if $a=b=c$. -/
theorem inequalities_603949 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / (b ^ 2 - b * c + c ^ 2) + b ^ 3 / (c ^ 2 - c * a + a ^ 2) +
    c ^ 3 / (a ^ 2 - a * b + b ^ 2) ≥ a + b + c ∧ (a ^ 3 / (b ^ 2 - b * c + c ^ 2) + b ^ 3 / (c ^ 2 - c * a + a ^ 2) +
    c ^ 3 / (a ^ 2 - a * b + b ^ 2) = a + b + c ↔ (a = b ∧ b = c)):= by
  -- Cauchy-Schwarz inequality for 3D vectors
  have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
    (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
    intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
    have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
    linarith

  -- Proving that the sum of products is positive
  have h2 : a * (b ^ 2 - b * c + c ^ 2) + b * (c ^ 2 - c * a + a ^ 2) + c * (a ^ 2 - a * b + b ^ 2) > 0:= by
    have g1 : a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 ≥ 0:= by positivity
    have g2 : a * b * c > 0:= by positivity
    linarith

  -- Proving that the denominators are positive
  have g1 : b ^ 2 - b * c + c ^ 2 > 0:= by
    have g1 : (b - c) ^ 2 ≥ 0:= by positivity
    have g2 : b * c > 0:= by positivity
    linarith
  have g2 : c ^ 2 - c * a + a ^ 2 > 0:= by
    have g1 : (c - a) ^ 2 ≥ 0:= by positivity
    have g2 : c * a > 0:= by positivity
    linarith
  have g3 : a ^ 2 - a * b + b ^ 2 > 0:= by
    have g1 : (a - b) ^ 2 ≥ 0:= by positivity
    have g2 : a * b > 0:= by positivity
    linarith

  -- Applying Cauchy-Schwarz inequality with specific values
  specialize h1 √(a * (b ^ 2 - b * c + c ^ 2)) √(b * (c ^ 2 - c * a + a ^ 2)) √(c * (a ^ 2 - a * b + b ^ 2)) √((a ^ 3 / (b ^ 2 - b * c + c ^ 2))) √(b ^ 3 / (c ^ 2 - c * a + a ^ 2)) √(c ^ 3 / (a ^ 2 - a * b + b ^ 2)) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

  -- Simplifying the square roots in the inequality
  rw [Real.sq_sqrt (by positivity)] at h1
  rw [Real.sq_sqrt (by positivity)] at h1
  rw [Real.sq_sqrt (by positivity)] at h1
  rw [Real.sq_sqrt (by positivity)] at h1
  rw [Real.sq_sqrt (by positivity)] at h1
  rw [Real.sq_sqrt (by positivity)] at h1

  -- Simplifying products of square roots
  rw [show √(a * (b ^ 2 - b * c + c ^ 2)) * √(a ^ 3 / (b ^ 2 - b * c + c ^ 2)) = √(a * (b ^ 2 - b * c + c ^ 2) * a ^ 3 / (b ^ 2 - b * c + c ^ 2)) by field_simp] at h1
  rw [show √(b * (c ^ 2 - c * a + a ^ 2)) * √(b ^ 3 / (c ^ 2 - c * a + a ^ 2)) = √(b * (c ^ 2 - c * a + a ^ 2) * b ^ 3 / (c ^ 2 - c * a + a ^ 2)) by field_simp] at h1
  rw [show √(c * (a ^ 2 - a * b + b ^ 2)) * √(c ^ 3 / (a ^ 2 - a * b + b ^ 2)) = √(c * (a ^ 2 - a * b + b ^ 2) * c ^ 3 / (a ^ 2 - a * b + b ^ 2)) by field_simp] at h1

  -- Further algebraic simplifications
  rw [show a * (b ^ 2 - b * c + c ^ 2) * a ^ 3 / (b ^ 2 - b * c + c ^ 2) = (a ^ 2) ^ 2 by field_simp ; linarith] at h1
  rw [show b * (c ^ 2 - c * a + a ^ 2) * b ^ 3 / (c ^ 2 - c * a + a ^ 2) = (b ^ 2) ^ 2 by field_simp ; linarith] at h1
  rw [show c * (a ^ 2 - a * b + b ^ 2) * c ^ 3 / (a ^ 2 - a * b + b ^ 2) = (c ^ 2) ^ 2 by field_simp ; linarith] at h1
  rw [show √((a ^ 2) ^ 2) = a ^ 2 by field_simp] at h1
  rw [show √((b ^ 2) ^ 2) = b ^ 2 by field_simp] at h1
  rw [show √((c ^ 2) ^ 2) = c ^ 2 by field_simp] at h1

  -- Helper lemma for the equality case analysis
  have h3 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a ≥ b → b ≥ c → (-a ^ 2 + b ^ 2 + c ^ 2) * (b - c) ^ 2 + (-b ^ 2 + c ^ 2 + a ^ 2) * (c - a) ^ 2 + (-c ^ 2 + a ^ 2 + b ^ 2) * (a - b) ^ 2 ≥ 0 ∧ ((-a ^ 2 + b ^ 2 + c ^ 2) * (b - c) ^ 2 + (-b ^ 2 + c ^ 2 + a ^ 2) * (c - a) ^ 2 + (-c ^ 2 + a ^ 2 + b ^ 2) * (a - b) ^ 2 = 0 → a = b ∧ b = c):= by
    intro a b c ha hb hc hab hbc
    have g1 : -c ^ 2 + a ^ 2 + b ^ 2 ≥ 0:= by nlinarith only [ha, hb, hc, hab, hbc]
    have g2 : -b ^ 2 + c ^ 2 + a ^ 2 ≥ 0:= by nlinarith only [ha, hb, hc, hab, hbc]
    replace g1 : (-c ^ 2 + a ^ 2 + b ^ 2) * (a - b) ^ 2 ≥ 0:= by positivity
    have g3 : (c - a) ^ 2 ≥ (b - c) ^ 2:= by nlinarith only [hab, hbc]
    replace g2 : (-b ^ 2 + c ^ 2 + a ^ 2) * (c - a) ^ 2 ≥ (-b ^ 2 + c ^ 2 + a ^ 2) * (b - c) ^ 2:= by exact mul_le_mul_of_nonneg_left g3 g2
    have g4 : c ^ 2 * (b - c) ^ 2 ≥ 0:= by positivity
    constructor
    .
      linarith
    .
      intro h
      replace g4 : c ^ 2 * (b - c) ^ 2 = 0:= by linarith
      replace g1 : (-c ^ 2 + a ^ 2 + b ^ 2) * (a - b) ^ 2 = 0:= by linarith
      simp at g4
      rcases g4 with g4 | g4
      .
        linarith
      .
        replace g4 : b = c:= by linarith
        subst b
        simp at g1
        rcases g1 with g1 | g1
        .
          linarith
        .
          simp
          linarith

  -- Considering all possible orderings of a, b, c
  have h4 : (a ≥ b ∧ b ≥ c) ∨ (a ≥ c ∧ c ≥ b) ∨ (b ≥ a ∧ a ≥ c) ∨ (b ≥ c ∧ c ≥ a) ∨ (c ≥ a ∧ a ≥ b) ∨ (c ≥ b ∧ b ≥ a):= by
    clear ha hb hc h1 h2 h3 g1 g2 g3
    by_cases h1 : a ≥ b
    .
      by_cases h2 : b ≥ c
      .
        tauto
      .
        simp at h2
        replace h2 : b ≤ c:= by linarith
        by_cases h3 : c ≥ a
        .
          tauto
        .
          simp at h3
          replace h3 : c ≤ a:= by linarith
          tauto
    .
      simp at h1
      replace h1 : a ≤ b:= by linarith
      by_cases h2 : b ≤ c
      .
        tauto
      .
        simp at h2
        replace h2 : b ≥ c:= by linarith
        by_cases h3 : c ≥ a
        .
          tauto
        .
          simp at h3
          replace h3 : c ≤ a:= by linarith
          tauto

  -- Proving the main inequality and the equality case
  constructor
  .
    -- Proving the inequality part
    suffices (a * (b ^ 2 - b * c + c ^ 2) + b * (c ^ 2 - c * a + a ^ 2) + c * (a ^ 2 - a * b + b ^ 2)) * (a ^ 3 / (b ^ 2 - b * c + c ^ 2) + b ^ 3 / (c ^ 2 - c * a + a ^ 2) + c ^ 3 / (a ^ 2 - a * b + b ^ 2)) ≥ ((a * (b ^ 2 - b * c + c ^ 2) + b * (c ^ 2 - c * a + a ^ 2) + c * (a ^ 2 - a * b + b ^ 2))) * (a + b + c) by exact le_of_mul_le_mul_left this h2
    suffices (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ ((a * (b ^ 2 - b * c + c ^ 2) + b * (c ^ 2 - c * a + a ^ 2) + c * (a ^ 2 - a * b + b ^ 2))) * (a + b + c) by linarith
    clear h1 h2 g1 g2 g3
    rcases h4 with h4 | h4 | h4 | h4 | h4 | h4
    all_goals
      rcases h4 with ⟨h4, h5⟩
    .
      replace h3:= (h3 a b c ha hb hc h4 h5).1
      linarith
    .
      replace h3:= (h3 a c b ha hc hb h4 h5).1
      linarith
    .
      replace h3:= (h3 b a c hb ha hc h4 h5).1
      linarith
    .
      replace h3:= (h3 b c a hb hc ha h4 h5).1
      linarith
    .
      replace h3:= (h3 c a b hc ha hb h4 h5).1
      linarith
    .
      replace h3:= (h3 c b a hc hb ha h4 h5).1
      linarith
  .
    -- Proving the equality case
    constructor
    .
      intro h5
      replace h5 : (a * (b ^ 2 - b * c + c ^ 2) + b * (c ^ 2 - c * a + a ^ 2) + c * (a ^ 2 - a * b + b ^ 2)) * (a ^ 3 / (b ^ 2 - b * c + c ^ 2) + b ^ 3 / (c ^ 2 - c * a + a ^ 2) + c ^ 3 / (a ^ 2 - a * b + b ^ 2)) = ((a * (b ^ 2 - b * c + c ^ 2) + b * (c ^ 2 - c * a + a ^ 2) + c * (a ^ 2 - a * b + b ^ 2))) * (a + b + c):= by rw [h5]
      rw [h5] at h1
      clear h5 h2 g1 g2 g3
      rcases h4 with h4 | h4 | h4 | h4 | h4 | h4
      all_goals
        rcases h4 with ⟨h4, h5⟩
      .
        have h2:= (h3 a b c ha hb hc h4 h5).1
        exact ((h3 a b c ha hb hc h4 h5).2) (by linarith)
      .
        have h2:= (h3 a c b ha hc hb h4 h5).1
        replace h3:= ((h3 a c b ha hc hb h4 h5).2) (by linarith)
        rcases h3 with ⟨h31, h32⟩
        refine ⟨(by linarith), (by linarith)⟩
      .
        have h2:= (h3 b a c hb ha hc h4 h5).1
        replace h3:= ((h3 b a c hb ha hc h4 h5).2) (by linarith)
        rcases h3 with ⟨h31, h32⟩
        refine ⟨(by linarith), (by linarith)⟩
      .
        have h2:= (h3 b c a hb hc ha h4 h5).1
        replace h3:= ((h3 b c a hb hc ha h4 h5).2) (by linarith)
        rcases h3 with ⟨h31, h32⟩
        refine ⟨(by linarith), (by linarith)⟩
      .
        have h2:= (h3 c a b hc ha hb h4 h5).1
        replace h3:= ((h3 c a b hc ha hb h4 h5).2) (by linarith)
        rcases h3 with ⟨h31, h32⟩
        refine ⟨(by linarith), (by linarith)⟩
      .
        have h2:= (h3 c b a hc hb ha h4 h5).1
        replace h3:= ((h3 c b a hc hb ha h4 h5).2) (by linarith)
        rcases h3 with ⟨h31, h32⟩
        refine ⟨(by linarith), (by linarith)⟩
    .
      intro h5
      rcases h5 with ⟨h51, h52⟩
      subst a b
      ring_nf
      field_simp
      ring_nf
