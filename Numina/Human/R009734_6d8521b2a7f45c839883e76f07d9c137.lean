import Mathlib

/- Do there exist pairwise distinct rational numbers $x, y$ and $z$ such that

$$
\frac{1}{(x-y)^{2}}+\frac{1}{(y-z)^{2}}+\frac{1}{(z-x)^{2}}=2014 ?
$$

Answer: No. -/
theorem number_theory_238242 :
    ¬∃ x y z : ℚ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ 1 / (x - y) ^ 2 + 1 / (y - z) ^ 2 + 1 / (z - x) ^ 2 = 2014 := by
  -- Let a = x - y, b = y - z.
  by_contra!
  obtain ⟨x, y, z, h₁, h₂, h₃, h₄⟩ := this
  let a := x - y
  let b := y - z
  -- The equation becomes 1/a² + 1/b² + 1/(a+b)² = 2014.
  rw [show x - y = a by rfl, show y - z = b by rfl, show z - x = -a - b by ring] at h₄
  -- Show that a ≠ 0, b ≠ 0 and a + b ≠ 0.
  have h₅ : a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩
    · by_contra!; absurd h₁; ring_nf at this; linarith
    · by_contra!; absurd h₂; ring_nf at this; linarith
    · by_contra!; absurd h₃; ring_nf at this; linarith
  -- The equation becomes ((a²+b²+ab)/(ab(a+b)))² = 2014.
  replace h₅ : ((a ^ 2 + b ^ 2 + a * b) / (a * b * (a + b))) ^ 2 = 2014 := by
    rw [<-h₄, <-neg_sub, neg_sq, sub_neg_eq_add, add_comm b a]
    field_simp [h₅]
    ring
  -- However, 2014 is not a square.
  have h₆ : IsSquare ((2014 : ℕ) : ℚ) := by
    simp [IsSquare]
    use ((a ^ 2 + b ^ 2 + a * b) / (a * b * (a + b)))
    rw [<-pow_two, h₅]
  rw [Rat.isSquare_natCast_iff] at h₆
  simp [IsSquare] at h₆
  obtain ⟨r, h₆⟩ := h₆
  linarith only [show 44 < r by nlinarith, show r < 45 by nlinarith]
