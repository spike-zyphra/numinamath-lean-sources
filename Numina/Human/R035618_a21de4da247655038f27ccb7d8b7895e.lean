import Mathlib

open Real

/- ## Task A-3.3.

Determine all pairs of real numbers $(x, y)$ for which


$$

\sin \left(x^{2}-5 y\right)-1 \geqslant \frac{x^{4}}{2016}

$$
 -/
theorem inequalities_241100 (x y : ℝ) :
  x^4 / 2016 ≤ sin (x^2 - 5 * y) - 1 ↔
  ∃ k : ℤ, (x = 0 ∧ y = -π/10 - 2*k*π/5)
  := by
    -- We'll chain iffs
    calc x^4 / 2016 ≤ sin (x^2 - 5 * y) - 1
    --
    _ ↔ sin (x^2 - 5 * y) - 1 = 0 ∧ x^4 / 2016 = 0 := by
      constructor
      · intro aa
        -- RHS is always ≤ 0
        have lee : sin (x ^ 2 - 5 * y) - 1 ≤ 0
        · simp only [tsub_le_iff_right, zero_add]
          exact sin_le_one (x ^ 2 - 5 * y)

        -- LHS is always 0 ≤
        have lee' : 0 ≤ x ^ 4 / 2016 := by positivity
        have yeah := le_antisymm lee <| le_trans lee' aa

        -- So then we know that both must be 0
        constructor
        · exact yeah
        · exact le_antisymm (yeah ▸ aa) lee'
      · intro ⟨aa, bb⟩
        rw [aa, bb]

    -- Simplify
    _ ↔ sin (x^2 - 5 * y) = 1 ∧ x = 0 := by
      simp only [div_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        or_false, and_congr_left_iff]
      exact fun _ => ⟨fun aa => by linarith, fun aa => by linarith⟩

    -- sin (x^2 - 5 * y) = 1 gives us a value for k
    _ ↔ ∃ k : ℤ, (x = 0 ∧ y = -π/10 - 2*k*π/5) := by
        simp only [exists_and_left]
        constructor
        · intro ⟨aa, bb⟩
          simp only [bb, true_and]
          rw [bb] at aa
          obtain ⟨k, dd⟩ := Real.sin_eq_one_iff.mp aa
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub] at dd
          exact ⟨k, by linarith⟩
        · simp only [and_imp, forall_exists_index]
          intro aa bb cc
          simp [cc, aa]
          ring_nf
          convert_to sin (π * (-1 / 2) - π * ↑bb * 2) = -1 using 0
          · exact neg_eq_iff_eq_neg
          apply Real.sin_eq_neg_one_iff.mpr
          refine ⟨-bb, ?_⟩
          field_simp
          linarith