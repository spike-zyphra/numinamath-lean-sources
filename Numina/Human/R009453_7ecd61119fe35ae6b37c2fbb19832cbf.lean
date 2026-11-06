import Mathlib
/- Déterminer la plus grande valeur possible et la plus petite valeur possible de

$$
\sqrt{4-a^{2}}+\sqrt{4-b^{2}}+\sqrt{4-c^{2}}
$$

lorsque $a, b, c$ sont des réels strictement positifs vérifiant $a^{2}+b^{2}+c^{2}=6$. -/
theorem inequalities_607513 :
IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 4 - a ^ 2 ≥ 0 ∧ 4 - b ^ 2 ≥ 0 ∧ 4 - c ^ 2 ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6 ∧ x = √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)} (3 * √2) ∧
IsLeast {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 4 - a ^ 2 ≥ 0 ∧ 4 - b ^ 2 ≥ 0 ∧ 4 - c ^ 2 ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6 ∧ x = √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)} (2 + √2):= by
  constructor
  .
    constructor
    .
      simp
      use √2
      simp
      use √2
      simp
      use √2
      simp
      norm_num
      linarith
    .
      simp [upperBounds]
      intro x a _ b _ c _ ha1 hb1 hc1 h hx
      subst x
      have h1 : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2):= by
        intro x y z
        have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0:= by positivity
        linarith
      specialize h1 (√(4 - a ^ 2)) (√(4 - b ^ 2)) (√(4 - c ^ 2))
      rw [Real.sq_sqrt (by linarith)] at h1
      rw [Real.sq_sqrt (by linarith)] at h1
      rw [Real.sq_sqrt (by linarith)] at h1
      rw [show 3 * (4 - a ^ 2 + (4 - b ^ 2) + (4 - c ^ 2)) = 18 by linarith] at h1
      rw [show (18 : ℝ) = (3 * √2) ^ 2 by ring_nf ; field_simp ; linarith] at h1
      replace h1 : |√(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)| ≤ |3 * √2|:= by exact sq_le_sq.mp h1
      rw [show |√(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2)| = √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2) by exact abs_of_nonneg (by positivity)] at h1
      rw [show |3 * √2| = 3 * √2 by exact abs_of_nonneg (by positivity)] at h1
      exact h1
  .
    constructor
    .
      simp
      use 0
      simp
      use √2
      simp
      use 2
      simp
      norm_num
      rw [show (4 : ℝ) = 2 ^ 2 by ring_nf]
      field_simp
    .
      simp [lowerBounds]
      intro x a ha b hb c hc ha1 hb1 hc1 h hx
      subst x
      have h1 : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 4 - a ^ 2 ≥ 0 ∧ 4 - b ^ 2 ≥ 0 ∧ 4 - c ^ 2 ≥ 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6 ∧ a ^ 2 ≤ 2 → √(4 - a ^ 2) + √(4 - b ^ 2) + √(4 - c ^ 2) ≥ 2 + √2:= by
        intro a b c ⟨_, _, _, ha1, hb1, hc1, h, hx⟩
        have h1 : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → √x + √y ≥ √(x + y):= by
          intro x y hx hy
          have h1 : (√x + √y) ^ 2 ≥ (√(x + y)) ^ 2:= by
            ring_nf
            rw [Real.sq_sqrt (by linarith)]
            rw [Real.sq_sqrt (by linarith)]
            rw [Real.sq_sqrt (by linarith)]
            have h1 : √x * √y ≥ 0:= by positivity
            linarith
          replace h1 : |√x + √y| ≥ |√(x + y)|:= by exact sq_le_sq.mp h1
          rw [show |√x + √y| = √x + √y by exact abs_of_nonneg (by positivity)] at h1
          rw [show |√(x + y)| = √(x + y) by exact abs_of_nonneg (by positivity)] at h1
          exact h1
        specialize h1 (4 - b ^ 2) (4 - c ^ 2) (by linarith) (by linarith)
        rw [show (4 - b ^ 2) + (4 - c ^ 2) = 2 + a ^ 2 by linarith] at h1
        suffices √(4 - a ^ 2) + √(2 + a ^ 2) ≥ 2 + √2 by linarith
        clear h1 h hb1 hc1
        rw [Eq.symm (abs_of_nonneg (show √(4 - a ^ 2) + √(2 + a ^ 2) ≥ 0 by positivity))]
        rw [Eq.symm (abs_of_nonneg (show 2 + √2 ≥ 0 by positivity))]
        suffices (√(4 - a ^ 2) + √(2 + a ^ 2)) ^ 2 ≥ (2 + √2) ^ 2 by exact sq_le_sq.mp this
        ring_nf
        field_simp
        ring_nf
        suffices √(4 - a ^ 2) * √(2 + a ^ 2) ≥ 2 * √2 by linarith
        rw [show √(4 - a ^ 2) * √(2 + a ^ 2) = √((4 - a ^ 2) * (2 + a ^ 2)) by field_simp]
        rw [show 2 * √2 = √(2 ^ 2 * 2) by field_simp]
        suffices (4 - a ^ 2) * (2 + a ^ 2) ≥ 2 ^ 2 * 2 by exact Real.sqrt_le_sqrt this
        suffices a ^ 2 * (2 - a ^ 2) ≥ 0 by linarith
        replace hx : 2 - a ^ 2 ≥ 0:= by linarith
        positivity
      have h2 : a ^ 2 ≤ 2 ∨ b ^ 2 ≤ 2 ∨ c ^ 2 ≤ 2:= by
        by_contra H
        simp at H
        rcases H with ⟨H1, H2, H3⟩
        linarith
      rcases h2 with h2 | h2 | h2
      .
        exact h1 a b c ⟨ha, hb, hc, (by linarith), (by linarith), (by linarith), h, h2⟩
      .
        specialize h1 b c a ⟨hb, hc, ha, (by linarith), (by linarith), (by linarith), (by linarith), h2⟩
        linarith
      .
        specialize h1 c a b ⟨hc, ha, hb, (by linarith), (by linarith), (by linarith), (by linarith), h2⟩
        linarith
