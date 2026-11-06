import Mathlib

open Polynomial

/- If a real function tends to some filter at -∞ and ∞, then it tends to that
  filter at complements to compact sets. -/
lemma Filter_Tendsto_cocompact_of_atBot_of_atTop {f : ℝ → ℝ} {l : Filter ℝ}
  (h1 : Filter.Tendsto f Filter.atTop l)
  (h2 : Filter.Tendsto f Filter.atBot l)
  : Filter.Tendsto f (Filter.cocompact ℝ) l := by
    simp_all only [cocompact_eq_atBot_atTop, Filter.tendsto_sup, and_self]

/- For natural numbers with an added ⊥ element, the number is either ⊥, 0, or positive-/
lemma Nat_WithBot_pos_cases (a : WithBot ℕ)
: a = ⊥ ∨ a = 0 ∨ 0 < a := by
  cases' a with a'
  · tauto
  · by_cases h : a' = 0
    · tauto
    · norm_num
      omega

/- If a polynomial has no roots, then the polynomial has a minimal element which is positive
  or a maximal element which is negative. -/
lemma Polynomial_minimum_or_maximum_of_ne_zero {p : Polynomial ℝ} (h : ∀ x, p.eval x ≠ 0)
  : ∃ x, (0 < p.eval x ∧ (∀ i, p.eval x ≤ p.eval i) ∨ p.eval x < 0 ∧ (∀ i, p.eval i ≤ p.eval x)) := by
    -- consider special cases of degree of p
    rcases Nat_WithBot_pos_cases p.degree with deg | deg | deg
    -- in one case p is 0
    · have p_eq : p = 0 := Polynomial.degree_eq_bot.mp deg
      -- but that's a contradiction
      norm_num [p_eq] at h
    -- in one case p is a constant
    · have eq_c := Polynomial.eq_C_of_degree_eq_zero deg
      -- which is trivially true, so choose 0 as the value
      exists 0
      rw [eq_c] at h ⊢
      norm_num at h ⊢
      tauto
    -- in the other cases, the degree of p is positive
    -- consider p'(x) = p(-x)
    · let p' := p.comp (-X)

      have p'_ne_zero : p' ≠ 0 := by
        simp only [ne_eq]
        rw [Polynomial.comp_eq_zero_iff]
        simp only [coeff_neg, coeff_X_zero, neg_zero, map_zero, neg_eq_zero, X_ne_zero,
          and_false, or_false]
        exact ne_zero_of_degree_gt deg


      -- then p' has a positive degree
      have deg' : 0 < p'.degree := by
        norm_num [p', Polynomial.degree_eq_natDegree p'_ne_zero, natDegree_comp]
        exact natDegree_pos_iff_degree_pos.mpr deg

      -- evaluating p' is the same as negating the argument then evaluating p
      have eval_eq_neg : p'.eval = p.eval ∘ Neg.neg := by
        ext i
        norm_num [p']

      -- p is continuous
      have eval_cont : Continuous (eval · p) := p.continuous

      -- consider signs of leading coefficient of p
      rcases le_total p.leadingCoeff 0 with h1 | h2
      -- if non-positive, then p(x) → -∞ when x → ∞
      · have tends_to_minus_infinity := p.tendsto_atBot_iff_leadingCoeff_nonpos.mpr ⟨deg, h1⟩
      -- consider signs of leading coefficient of p'
        rcases le_total p'.leadingCoeff 0 with nonpos | nonneg
        -- if non-positive, then p'(x) → -∞ when x → ∞
        · have tends_to_minus_infinity' := p'.tendsto_atBot_iff_leadingCoeff_nonpos.mpr ⟨deg', nonpos⟩

          -- so, then p(x) → -∞ when x → -∞
          rw [eval_eq_neg] at tends_to_minus_infinity'
          apply Filter.tendsto_map' at tends_to_minus_infinity'
          simp only [Filter.map_neg, Filter.neg_atTop] at tends_to_minus_infinity'

          -- so p(x) → -∞ on complements to compact sets
          have cocompact := Filter_Tendsto_cocompact_of_atBot_of_atTop tends_to_minus_infinity tends_to_minus_infinity'

          -- so there is some x which is an upper bound of p
          obtain ⟨x, x1⟩ := eval_cont.exists_forall_ge cocompact

          -- that's our upper bound
          exists x
          right
          refine ⟨?_, x1⟩

          -- now we just need to show that p(x) < 0

          -- we have some p(x') < 0
          obtain ⟨x', _, xh⟩ := Filter.exists_lt_of_tendsto_atBot tends_to_minus_infinity _ 0

          -- assume the opposite
          by_contra nonneg

          -- then there's some value where p is equal to 0
          obtain ⟨i, ih⟩ : ∃ i, eval i p = 0 := by
            have gt : 0 ≤ eval x p := by linarith
            have lt : eval x' p ≤ 0 := by linarith
            exact mem_range_of_exists_le_of_exists_ge eval_cont ⟨x', lt⟩ ⟨x, gt⟩

          -- but it shouldn't be equal to 0
          have ne_zero := h i

          -- which is a contradiction
          contradiction

        -- if non-negative, then p'(x) → ∞ when x → ∞
        · have tends_to_plus_infinity' := p'.tendsto_atTop_iff_leadingCoeff_nonneg.mpr ⟨deg', nonneg⟩

          -- so, then p(x) → ∞ when x → -∞
          rw [eval_eq_neg] at tends_to_plus_infinity'
          apply Filter.tendsto_map' at tends_to_plus_infinity'
          simp only [Filter.map_neg, Filter.neg_atTop] at tends_to_plus_infinity'

          -- but then p covers (-∞, ∞), so p is surjective
          have surj : (eval · p).Surjective := eval_cont.surjective' tends_to_plus_infinity' tends_to_minus_infinity

          -- so it contains 0
          obtain ⟨x, xh⟩ := surj 0

          -- but p doesn't contain 0
          have ne_zero := h x

          -- that's a contradiction
          contradiction

      -- if non-negative, then p(x) → ∞ when x → ∞
      · have tends_to_infinity := p.tendsto_atTop_iff_leadingCoeff_nonneg.mpr ⟨deg, h2⟩
        -- consider signs of leading coefficient of p'
        rcases le_total p'.leadingCoeff 0 with nonpos | nonneg
        -- if non-positive, then p'(x) → -∞ when x → ∞
        · have tends_to_minus_infinity' := p'.tendsto_atBot_iff_leadingCoeff_nonpos.mpr ⟨deg', nonpos⟩


          -- so, then p(x) → -∞ when x → -∞
          rw [eval_eq_neg] at tends_to_minus_infinity'
          apply Filter.tendsto_map' at tends_to_minus_infinity'
          simp only [Filter.map_neg, Filter.neg_atTop] at tends_to_minus_infinity'

          -- but then p covers (-∞, ∞), so p is surjective
          have surj : (eval · p).Surjective := eval_cont.surjective tends_to_infinity tends_to_minus_infinity'

          -- so it contains 0
          obtain ⟨x, xh⟩ := surj 0

          -- but p doesn't contain 0
          have ne_zero := h x

          -- that's a contradiction
          contradiction

        -- if non-negative, then p'(x) → ∞ when x → ∞
        · have tends_to_plus_infinity' := p'.tendsto_atTop_iff_leadingCoeff_nonneg.mpr ⟨deg', nonneg⟩

          -- so, then p(x) → ∞ when x → -∞
          rw [eval_eq_neg] at tends_to_plus_infinity'
          apply Filter.tendsto_map' at tends_to_plus_infinity'
          simp only [Filter.map_neg, Filter.neg_atTop] at tends_to_plus_infinity'

          -- so p(x) → ∞ on complements to compact sets
          have cocompact := Filter_Tendsto_cocompact_of_atBot_of_atTop tends_to_infinity tends_to_plus_infinity'

          -- so there is some x which is a lower bound of p
          obtain ⟨x, x1⟩ := eval_cont.exists_forall_le cocompact

          -- that's our lower bound
          exists x
          left
          refine ⟨?_, x1⟩

          -- now we just need to show that 0 < p(x)

          -- we have some  0 < p(x')
          obtain ⟨x', _, xh⟩ := Filter.exists_lt_of_tendsto_atTop tends_to_infinity 0 0

          -- assume the opposite
          by_contra nonneg

          -- then there's some value where p is equal to 0
          obtain ⟨i, ih⟩ : ∃ i, eval i p = 0 := by
            have gt : 0 ≤ eval x' p := by linarith
            have lt : eval x p ≤ 0 := by linarith
            exact mem_range_of_exists_le_of_exists_ge eval_cont ⟨x, lt⟩ ⟨x', gt⟩

          -- but it shouldn't be equal to 0
          have ne_zero := h i

          -- which is a contradiction
          contradiction

/- [ $\quad$ Functions. Continuity (other) $\quad$ Proof by contradiction $]$

Authors: Geovvanov A.S., Drichriev O., Sukhov K.

Given a polynomial $P(x)$ and numbers $a_{1}, a_{2}, a_{3}, b_{1}, b_{2}, b_{3}$, such that $a_{1} a_{2} a_{3} \neq 0$. It turns out that $P\left(a_{1} x+b_{1}\right)+P\left(a_{2} x+\right.$ $\left.b_{2}\right)=P\left(a_{3} x+b_{3}\right)$ for any real $x$. Prove that $P(x)$ has at least one real root. -/
theorem algebra_170698 {P : Polynomial ℝ} {a b : Fin 3 → ℝ}
    (ha : a 0 * a 1 * a 2 ≠ 0)
    (h : ∀ x, P.eval (a 0 * x + b 0) + P.eval (a 1 * x + b 1) = P.eval (a 2 * x + b 2)) :
    ∃ x, P.eval x = 0 := by
      -- assume the opposite
      by_contra ne_zero

      -- then every value of p is non-zero
      replace ne_zero : ∀ (x : ℝ), ¬eval x P = 0 := by aesop

      -- we have that no a values are zero
      have ne_zero_0 : a 0 ≠ 0 := by norm_num at ha; tauto
      have ne_zero_1 : a 1 ≠ 0 := by norm_num at ha; tauto
      have ne_zero_2 : a 2 ≠ 0 := by norm_num at ha; tauto

      -- p is either always positive or always negative, because it's never zero
      rcases Polynomial_minimum_or_maximum_of_ne_zero ne_zero with ⟨x, ⟨pos, h1⟩ | ⟨neg, h2⟩⟩
      -- let x0 be a value such that x = a_2 * x0 + b_2
      · obtain ⟨x0, xh⟩ : ∃ x0, x = a 2 * x0 + b 2 := by
          exists (x - b 2) / a 2
          field_simp

        -- we have 2 * P(x) ≤ P(a 0 * x0 + b 0) + P(a 1 * x0 + b 1)
        have lee : 2 * eval x P ≤ eval (a 0 * x0 + b 0) P + eval (a 1 * x0 + b 1) P := by
          -- because P(x) is the minimum
          have left_le : eval x P ≤ eval (a 0 * x0 + b 0) P := h1 _
          have right_le : eval x P ≤ eval (a 1 * x0 + b 1) P := h1 _
          linarith

        -- and P(x) < 2 * P(x), because P is positive
        have lt : eval x P < 2 * eval x P := by linarith

        -- but hypothesis says that P(x) = P(a 0 * x0 + b 0) + P(a 1 * x0 + b 1)
        have eq : eval x P = eval (a 0 * x0 + b 0) P + eval (a 1 * x0 + b 1) P := by
          rw [xh]
          exact (h x0).symm

        -- but those inequalities are not compatible, contradiction
        linarith
      -- let x0 be a value such that x = a_2 * x0 + b_2
      · obtain ⟨x0, xh⟩ : ∃ x0, x = a 2 * x0 + b 2 := by
          exists (x - b 2) / a 2
          field_simp
        -- we have P(a 0 * x0 + b 0) + P(a 1 * x0 + b 1) ≤ 2 * P(x)
        have lee : eval (a 0 * x0 + b 0) P + eval (a 1 * x0 + b 1) P ≤ 2 * eval x P := by
          -- because P(x) is the maximum
          have left_le : eval (a 0 * x0 + b 0) P ≤ eval x P := h2 _
          have right_le : eval (a 1 * x0 + b 1) P ≤ eval x P := h2 _
          linarith

        -- and 2 * P(x) < P(x), because P is negative
        have lt : 2 * eval x P < eval x P := by linarith

        -- but hypothesis says that P(x) = P(a 0 * x0 + b 0) + P(a 1 * x0 + b 1)
        have eq : eval x P = eval (a 0 * x0 + b 0) P + eval (a 1 * x0 + b 1) P := by
          rw [xh]
          exact (h x0).symm

        -- but those inequalities are not compatible, contradiction
        linarith