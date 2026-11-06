import Mathlib
/- Prove that for all non-negative real numbers $x, y, z$, not all zero, the following inequality holds:

$$
\frac{2 x^{2}-x+y+z}{x+y^{2}+z^{2}}+\frac{2 y^{2}+x-y+z}{x^{2}+y+z^{2}}+\frac{2 z^{2}+x+y-z}{x^{2}+y^{2}+z} \geqslant 3
$$

Determine all triplets $(x, y, z)$ for which the above inequality is an equality. -/
theorem inequalities_129106 : (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) → (2 * x ^ 2 - x + y + z) / (x + y ^ 2 + z ^ 2) + (2 * y ^ 2 + x - y + z) / (x ^ 2 + y + z ^ 2) + (2 * z ^ 2 + x + y - z) / (x ^ 2 + y ^ 2 + z) ≥ 3) ∧ {(x, y, z) : ℝ × ℝ × ℝ | 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ (2 * x ^ 2 - x + y + z) / (x + y ^ 2 + z ^ 2) + (2 * y ^ 2 + x - y + z) / (x ^ 2 + y + z ^ 2) + (2 * z ^ 2 + x + y - z) / (x ^ 2 + y ^ 2 + z) = 3} = {(x, y, z) : ℝ × ℝ × ℝ | ∃ t : ℝ, t > 0 ∧ (x, y, z) = (t, t, t)} ∪ {(x, y, z) : ℝ × ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ((x, y, z) = (t, t, 1 - t) ∨ (x, y, z) = (1 - t, t, t) ∨ (x, y, z) = (t, 1 - t, t))}:= by
  -- Helper lemma: For positive A, B, C, we have (B+C-A)/A + (C+A-B)/B + (A+B-C)/C ≥ 3
  -- with equality iff A = B = C
  have h1 : ∀ A B C : ℝ, A > 0 → B > 0 → C > 0 → ((B + C - A) / A + (C + A - B) / B + (A + B - C) / C ≥ 3 ∧ ((B + C - A) / A + (C + A - B) / B + (A + B - C) / C = 3 → (A = B ∧ B = C))):= by
    intro A B C hA hB hC
    -- Another helper lemma: For positive x, y, we have x/y + y/x ≥ 2 with equality iff x = y
    have h : ∀ x y : ℝ, x > 0 → y > 0 → (x / y + y / x ≥ 2 ∧ (x / y + y / x = 2 → x = y)):= by
      intro x y hx hy
      constructor
      .
        suffices h1 : x / y + y / x - 2 ≥ 0 by linarith
        rw [show x / y + y / x - 2 = (x - y) ^ 2 / (x * y) by field_simp ; linarith]
        positivity
      .
        intro h
        replace h : x / y + y / x - 2 = 0:= by linarith
        rw [show x / y + y / x - 2 = (x - y) ^ 2 / (x * y) by field_simp ; linarith] at h
        simp [show x ≠ 0 by linarith, show y ≠ 0 by linarith] at h
        linarith
    constructor
    .
      rw [show (B + C - A) / A = B / A + C / A - 1 by field_simp]
      rw [show (C + A - B) / B = C / B + A / B - 1 by field_simp]
      rw [show (A + B - C) / C = A / C + B / C - 1 by field_simp]
      obtain ⟨g1, _⟩:= h A B hA hB
      obtain ⟨g2, _⟩:= h A C hA hC
      obtain ⟨g3, _⟩:= h B C hB hC
      linarith
    .
      intro h1
      rw [show (B + C - A) / A = B / A + C / A - 1 by field_simp] at h1
      rw [show (C + A - B) / B = C / B + A / B - 1 by field_simp] at h1
      rw [show (A + B - C) / C = A / C + B / C - 1 by field_simp] at h1
      obtain ⟨g1, g2⟩:= h A B hA hB
      obtain ⟨g3, g4⟩:= h A C hA hC
      obtain ⟨g5, _⟩:= h B C hB hC
      replace g2:= g2 (by linarith)
      replace g4:= g4 (by linarith)
      constructor
      all_goals
        linarith
  constructor
  .
    -- First part: Proving the inequality
    intro x y z hx hy hz hxyz
    -- Define A, B, C to match the form of our helper lemma
    set A:= x + y ^ 2 + z ^ 2 with hA
    set B:= x ^ 2 + y + z ^ 2 with hB
    set C:= x ^ 2 + y ^ 2 + z with hC
    clear_value A B C
    -- Rewrite the expressions to match our helper lemma
    rw [show 2 * x ^ 2 - x + y + z = B + C - A by linarith]
    rw [show 2 * y ^ 2 + x - y + z = C + A - B by linarith]
    rw [show 2 * z ^ 2 + x + y - z = A + B - C by linarith]
    -- Prove A, B, C are positive
    replace hA : A > 0:= by
      subst A
      rcases hxyz with hxyz | hxyz | hxyz
      all_goals
        positivity
    replace hB : B > 0:= by
      subst B
      rcases hxyz with hxyz | hxyz | hxyz
      all_goals
        positivity
    replace hC : C > 0:= by
      subst C
      rcases hxyz with hxyz | hxyz | hxyz
      all_goals
        positivity
    -- Apply the helper lemma to get the inequality
    exact (h1 A B C hA hB hC).1
  .
    -- Second part: Characterizing when equality holds
    ext ⟨x, y, z⟩
    constructor
    .
      -- Forward direction: If equality holds, then (x,y,z) is in our set
      intro h
      simp at h
      rcases h with ⟨hx, hy, hz, hxyz, h⟩
      set A:= x + y ^ 2 + z ^ 2 with hA
      set B:= x ^ 2 + y + z ^ 2 with hB
      set C:= x ^ 2 + y ^ 2 + z with hC
      clear_value A B C
      rw [show 2 * x ^ 2 - x + y + z = B + C - A by linarith] at h
      rw [show 2 * y ^ 2 + x - y + z = C + A - B by linarith] at h
      rw [show 2 * z ^ 2 + x + y - z = A + B - C by linarith] at h
      have hA1 : A > 0:= by
        subst A
        rcases hxyz with hxyz | hxyz | hxyz
        all_goals
          positivity
      have hB1 : B > 0:= by
        subst B
        rcases hxyz with hxyz | hxyz | hxyz
        all_goals
          positivity
      have hC1 : C > 0:= by
        subst C
        rcases hxyz with hxyz | hxyz | hxyz
        all_goals
          positivity
      -- From the helper lemma, equality means A = B = C
      replace h:= (h1 A B C hA1 hB1 hC1).2 h
      rcases h with ⟨h2, h3⟩
      subst A B C
      clear hA1 hB1 hC1 h1
      -- Derive conditions on x, y, z
      replace h2 : (x - y) * (x + y - 1) = 0:= by linarith
      replace h3 : (y - z) * (y + z - 1) = 0:= by linarith
      simp at h2 h3
      -- Case analysis on the possible values of x, y, z
      rcases h2 with h2 | h2
      .
        replace h2 : x = y:= by linarith
        subst x
        rcases h3 with h3 | h3
        .
          replace h3 : y = z:= by linarith
          subst y
          simp at hxyz
          simp
          left
          positivity
        .
          replace h3 : z = 1 - y:= by linarith
          subst z
          simp
          right
          use y
          refine ⟨by linarith, by linarith, by simp⟩
      .
        rcases h3 with h3 | h3
        .
          replace h3 : y = z:= by linarith
          subst y
          replace h2 : x = 1 - z:= by linarith
          subst x
          simp
          right
          use z
          refine ⟨by linarith, by linarith, by simp⟩
        .
          replace h2 : x = z:= by linarith
          subst x
          replace h3 : y = 1 - z:= by linarith
          subst y
          simp
          right
          use z
          refine ⟨by linarith, by linarith, by simp⟩
    .
      -- Reverse direction: If (x,y,z) is in our set, then equality holds
      intro h
      simp at h
      rcases h with h | h
      .
        -- Case 1: x = y = z > 0
        rcases h with ⟨t, h1, hx, hy, hz⟩
        subst x y z
        simp
        refine ⟨by positivity, by positivity, ?_⟩
        field_simp
        ring_nf
      .
        -- Case 2: (x,y,z) is one of the three special forms
        rcases h with ⟨t, h1, h2, h⟩
        have g : 1 - t + t ^ 2 * 2 > 0:= by
          rw [show 1 - t + t ^ 2 * 2 = 2 * (t - 1 / 4) ^ 2 + 7 / 8 by ring]
          positivity
        rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
        all_goals
          subst x y z
          simp
          refine ⟨by linarith, by linarith, ?_⟩
        .
          constructor
          .
            by_contra H
            simp at H
            rcases H with ⟨H1, H2⟩
            linarith
          .
            ring_nf
            field_simp
            ring_nf
        .
          constructor
          .
            by_contra H
            simp at H
            rcases H with ⟨H1, H2⟩
            linarith
          .
            ring_nf
            field_simp
            ring_nf
        .
          constructor
          .
            by_contra H
            simp at H
            linarith
          .
            constructor
            .
              by_contra H
              simp at H
              rcases H with ⟨H1, H2, _⟩
              linarith
            .
              ring_nf
              field_simp
              ring_nf
