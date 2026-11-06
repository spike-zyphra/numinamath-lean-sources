import Mathlib

open Real

/-
Let $a$ be an integer, and the two real roots of the equation
$x^{2}+(a-3) x+a^{2}=0$ be $x_{1}$ and $x_{2}$.
If $\tan \left(\arctan x_{1}+\arctan x_{2}\right)$ is also an integer,
then the number of such $a$ is ( ).
(A) 0
(B) 1
(C) 2
(D) 4
-/

theorem algebra_319252
    (x1 x2 Δ : ℝ → ℝ)
    (hx1 : ∀ a, x1 a = (3 - a - √((a - 3) ^ 2 - 4 * a ^2)) / 2)
    (hx2 : ∀ a, x2 a = (3 - a + √((a - 3) ^ 2 - 4 * a ^2)) / 2)
    (hΔ : ∀ a, Δ a = (a - 3) ^ 2 - 4 * a ^ 2)
    (S : Set ℤ)
    (hS : S = {a : ℤ |
      Δ a ≥ 0
      ∧ (∃ k : ℤ, tan (arctan (x1 a) + arctan (x2 a)) = k)
      ∧ (∀ l : ℤ, arctan (x1 a) + arctan (x2 a) ≠ (2 * l + 1) * π / 2)})
    : S.ncard = 1 := by

-- The expression $\tan(\arctan x_1 + \arctan x_2)$ simplifies to:
-- $$\frac{x_1 + x_2}{1 - x_1 x_2} = \frac{3 - a}{1 - a^2}
-- = \frac{3 - a}{(1 - a)(1 + a)} = \frac{a - 3}{(a - 1)(a + 1)}$$
  have h1 (a : ℤ) (ha1 : a ≠ 1) (ha2 : a ≠ -1) (ha : Δ a ≥ 0) :
      tan (arctan (x1 a) + arctan (x2 a)) = (a - 3) / ((a - 1) * (a + 1)) := by
-- The solutions satisfy the equation provided the discriminant is nonnegative.
    have g1 a (ha : Δ a ≥ 0) : x1 a ^ 2 + (a - 3) * x1 a + a ^ 2 = 0 := by
      rw [hΔ] at ha
      rw [hx1]
      ring_nf
      rw [sq_sqrt (by linarith)]
      linarith
    have g2 a (ha : Δ a ≥ 0) : x2 a ^ 2 + (a - 3) * x2 a + a ^ 2 = 0 := by
      rw [hΔ] at ha
      rw [hx2]
      ring_nf
      rw [sq_sqrt (by linarith)]
      linarith
    specialize g1 a ha
    specialize g2 a ha
    rw [hΔ] at ha
-- Using Vieta's formulas, we know:
    have e1 : x1 a + x2 a = 3 - a := by rw [hx1, hx2]; nlinarith
    have e2 : x1 a * x2 a = a ^ 2 := by nlinarith
    rw [tan_add']
    swap
    . split_ands <;> intro k1 <;> apply arctan_ne_mul_pi_div_two
    have c2 : (a - 1 : ℝ) ≠ 0 := by norm_cast; omega
    have c3 : (a + 1 : ℝ) ≠ 0 := by norm_cast; omega
    have c4 : (1 - a ^ 2 : ℝ) ≠ 0 := by
      intro d1
      replace d1 : (a ^ 2 : ℝ) = 1 := by linarith
      obtain d1 | d1 : a = (1 : ℝ) ∨ a = (-1 : ℝ) := sq_eq_one_iff.mp d1
      . simp [d1] at c2
      . simp [d1] at c3
    field_simp [e1, e2]
    ring_nf

-- For this fraction to be an integer, $(a - 1)(a + 1)$ must divide $a - 3$.
  have h2 (a : ℤ) (ha1 : a ≠ 1) (ha2 : a ≠ -1) : a ∈ S
      ↔ (Δ a ≥ 0
        ∧ ((a - 1) * (a + 1) ∣ a - 3)
        ∧ (∀ l : ℤ, arctan (x1 a) + arctan (x2 a) ≠ (2 * l + 1) * π / 2))
         := by
    have c3 : (a - 1 : ℝ) ≠ 0 := by norm_cast; omega
    have c4 : (a + 1 : ℝ) ≠ 0 := by norm_cast; omega
    constructor
    all_goals intro ha
    . rw [hS] at ha
      dsimp at ha
      obtain ⟨c1, ⟨k, c2⟩, c2'⟩ := ha
      split_ands
      . exact c1
      . specialize h1 a ha1 ha2 c1
        rw [c2] at h1
        use k
        field_simp at h1
        norm_cast at h1
        ring_nf at h1 ⊢
        omega
      . exact c2'
    . rw [hS]
      obtain ⟨c1, ⟨k, c2⟩, c2'⟩ := ha
      split_ands
      . exact c1
      . specialize h1 a ha1 ha2 c1
        use k
        rw [h1]
        field_simp
        norm_cast
        ring_nf at c2 ⊢
        omega
      . exact c2'

-- Additionally, the quadratic equation must have real roots,
-- so its discriminant must be non-negative:
-- $$(a - 3)^2 - 4a^2 \geq 0 \implies -3a^2 - 6a + 9 \geq 0 \implies (a + 3)(a - 1) \leq 0$$
-- This gives $a \in [-3, 1]$.
  have h3 a (ha : a ∈ S) : a ∈ Finset.Icc (-3) 1 := by
    obtain c1 | c1 | c1 : a = 1 ∨ a = -1 ∨ a ≠ 1 ∧ a ≠ -1 := by omega
    . simp; omega
    . simp; omega
    . rw [hS] at ha
      obtain ⟨c3, _⟩ := ha
      rw [hΔ] at c3
      norm_cast at c3
      replace c3 : -3 * a ^ 2 - 6 * a + 9 ≥ 0 := by linarith
      replace c3 : (a + 3) * (a - 1) ≤ 0 := by linarith
      have c4 : a + 3 ≥ 0 := by nlinarith
      have c5 : a - 1 ≤ 0 := by nlinarith
      simp
      omega

-- Checking integer values within this interval: Only $a = 0$ results in an integer value.
  have h4 a : a ∈ S ↔ a = 0 := by
    constructor
    . intro ha
      specialize h3 a ha
      simp at h3
      obtain ha1 | ha1 | ha1 : a = 1 ∨ a = -1 ∨ a ≠ 1 ∧ a ≠ -1 := by omega
      . subst ha1
        rw [hS] at ha
        obtain ⟨c1, ⟨k, c2⟩, c2'⟩ := ha
        specialize hx1 1
        specialize hx2 1
        norm_num at hx1 hx2 c2'
        rw [hx1, hx2, arctan_one] at c2'
        exfalso
        apply c2' 0
        ring_nf
      . subst ha1
        rw [hS] at ha
        obtain ⟨c1, ⟨k, c2⟩, c2'⟩ := ha
        specialize hx1 (-1)
        specialize hx2 (-1)
        norm_num at hx1 hx2 c2'
        rw [hx1, hx2] at c2'
        set x := (4 - √12) / 2
        have d1 : 4 - √12 > 0 := by
          suffices 4 > √12 from by linarith
          suffices 4 ^ 2 > √12 ^ 2 from by
            refine (sqrt_lt' ?_).mpr ?_ <;> norm_num
          norm_num
        have d2 : x > 0 := by dsimp [x]; linarith
        have c3 : (4 + √12) / 2 = x⁻¹ := by
          field_simp
          ring_nf
          rw [sq_sqrt (by norm_num)]
          ring_nf
        rw [c3] at c2'
        rw [arctan_inv_of_pos d2] at c2'
        specialize c2' 0
        simp at c2'
      obtain ⟨k, c1⟩ := (h2 a ha1.left ha1.right).mp ha
      obtain ha2 | ha2 | ha2 : a = -3 ∨ a = -2 ∨ a = 0 := by omega
      . subst ha2
        simp at c1
        omega
      . subst ha2
        simp at c1
        omega
      . exact ha2
    . intro ha
      subst ha
      specialize h2 0 (by norm_num) (by norm_num)
      suffices ∀ (l : ℤ), ¬arctan 3 = (2 * ↑l + 1) * π / 2 from by simpa [h2, hΔ, hx1, hx2]
      apply arctan_ne_mul_pi_div_two

-- Thus, the number of such $a$ is 1.
  have h5 : S.ncard = 1 := by
    have c1 : S = {0} := by ext a; simp [h4]
    simp [c1]

  exact h5
