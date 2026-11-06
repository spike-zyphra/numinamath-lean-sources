import Mathlib

open Polynomial

/- A quadratic polynomial has a root iff it's discriminant is positive. -/
lemma quadratic_exists_root_iff_discrim_nonneg {a b c : ℝ} (h : a ≠ 0)
  : (∃ x, a * (x * x) + b * x + c = 0) ↔ 0 ≤ discrim a b c := by
    constructor
    -- when we have a root
    · intro ⟨x, xh⟩
      -- assume discriminant is negative
      by_contra
      -- then the discriminant is not equal to a square
      have not_square : ∀ s, discrim a b c ≠ s ^ 2 := by
        intro s
        have sq_pos : 0 ≤ s ^ 2 := sq_nonneg s
        linarith

      -- then there's no root
      have no_root := quadratic_ne_zero_of_discrim_ne_sq not_square x

      -- which is a contradiction
      contradiction
    -- assume discriminant is positive
    · intro disc_pos
      -- then there's a root
      apply exists_quadratic_eq_zero
      -- because the leading coefficient is non-zero
      · exact h
      -- and we can express the discriminant as a square, ΔP = √(ΔP) * √(ΔP)
      · exists √(discrim a b c)
        exact (Real.mul_self_sqrt disc_pos).symm

/-
Problem 9.1. Let $f(x)=x^{2}+6 a x-a$ where $a$ is a real parameter.

a) Find all values of $a$ for which the equation $f(x)=0$ has at least one real root.

b) If $x_{1}$ and $x_{2}$ are the real roots of $f(x)=0$ (not necessarily distinct) find the least value of the expression


$$

A=\frac{9 a-4 a^{2}}{\left(1+x_{1}\right)\left(1+x_{2}\right)}-\frac{70 a^{3}+1}{\left(1-6 a-x_{1}\right)\left(1-6 a-x_{2}\right)}

$$

 -/
theorem algebra_295526 (f : ℝ → Polynomial ℝ) (hf : ∀ a, f a = X ^ 2 + C (6 * a) * X - C a) :
    (∀ a, ((∃ x, x ∈ (f a).roots) ↔ a ∈ (Set.Iic (-1 / 9) ∪ Set.Ici 0))) ∧
    IsLeast {x | ∃ a x1 x2: ℝ, (f a).roots = {x1, x2} ∧ x = (9 * a - 4 * a^2) / ((1 + x1) * (1 + x2)) -
      (70 * a^3 + 1) / ((1 - 6 * a - x1) * (1 - 6 * a - x2))} (-89 / 81) := by

        -- write the polynomial in normal form
        replace hf : ∀ a, f a = C 1 * X ^ 2 + C (6 * a) * X + C (-a) := by
          intro a
          rw [hf]
          simp only [map_mul, map_one, one_mul, map_neg]
          ring_nf

        -- the polynomial is non-zero
        have f_ne_zero : ∀ a, f a ≠ 0 := by
          intro a
          rw [hf]
          apply_fun (coeff · 2)
          norm_num

        -- we prove (a) first, that f_a(x) = 0 has at least one root when a ∈ (-∞, -1/9] ∪ [0, ∞)
        have mem : ∀ a, ((∃ x, x ∈ (f a).roots) ↔ a ∈ (Set.Iic (-1 / 9) ∪ Set.Ici 0)) := by
          intro a

          -- x is a root iff f(x) = 0
          trans ∃ x, eval x (f a) = 0
          · norm_num [f_ne_zero]

          -- there exists a root iff i.e. 0 ≤ 9 * a ^ 2 + a
          trans 0 ≤ 9 * a ^ 2 + a
          · norm_num [hf]

            -- because x is a root iff 1 * (x * x) + (6 * a) * x + (-a) = 0
            trans (∃ x, 1 * (x * x) + (6 * a) * x + (-a) = 0)
            · constructor
              all_goals
              · intro ⟨x, hx⟩
                exists x
                linarith

            -- consider the discriminant, which is (6 * a) ^ 2 + 4 * a
            have discrim_eq : discrim (1 : ℝ) (6 * a) (-a) = (6 * a) ^ 2 + 4 * a := by
              norm_num [discrim]

            -- there's a root iff the discriminant is non-negative
            trans 0 ≤ discrim (1 : ℝ) (6 * a) (-a)
            · exact quadratic_exists_root_iff_discrim_nonneg (by linarith)

            rw [discrim_eq]

            -- and the discriminant is positive iff 0 ≤ 9 * a ^ 2 + a
            constructor
            all_goals
            · intro aa
              linarith

          -- now we'll show that 0 ≤ 9 * a ^ 2 + a
          -- iff a ∈ (-∞, -1/9] ∪ [0, ∞)
          norm_num
          constructor
          -- consider when 0 ≤ 9 * a ^ 2 + a
          · intro aa
            -- we have that 0 ≤ a * (a + 1 / 9)
            replace aa : 0 ≤ a * (a + 1 / 9) := by linarith
            -- when a is positive we're done
            by_cases ha : 0 ≤ a
            · tauto
            -- when a is negative, then (a + 1 / 9) is non-positive
            · simp [mul_nonneg_iff, ha] at aa
              -- so then a ≤ -(1 / 9)
              left
              linarith
          -- consider when a ∈ (-∞, -1/9] ∪ [0, ∞), then 0 ≤ 9 * a ^ 2 + a holds
          · rintro (aa | bb) <;> nlinarith

        -- so we're done with (a)
        refine ⟨mem, ?_⟩

        -- now we'll solve (b)

        -- the equation for A can be simplified
        have set_eq : {A | ∃ a x1 x2: ℝ, (f a).roots = {x1, x2} ∧ A = (9 * a - 4 * a^2) / ((1 + x1) * (1 + x2)) -
      (70 * a^3 + 1) / ((1 - 6 * a - x1) * (1 - 6 * a - x2))}
          = {A | ∃ a x1 x2: ℝ, (f a).roots = {x1, x2} ∧ (((A = 10 * (a * a) + 2 * a - 1) ∧ 1 - 7 * a ≠ 0) ∨ (A = 0 ∧ 1 - 7 * a = 0))} := by

            -- we have A, a, r1, r2, and that r1 and r2 are roots of f_a
            ext A
            refine exists_congr ?_
            intro a
            refine exists_congr ?_
            intro r1
            refine exists_congr ?_
            intro r2
            simp only [and_congr_right_iff]
            intro roots

            -- the degree of f_a is 2
            have f_degree : (f a).natDegree = 2 := by
              rw [hf]
              refine natDegree_quadratic ?_
              linarith

            -- f_a has 2 roots
            have f_roots_card : (f a).roots.card = 2 := by
              rw [roots]
              norm_num

            -- so it's degree is equal to it's number of roots
            have f_degree_eq_roots_card : (f a).roots.card = (f a).natDegree := by linarith

            -- so we can split it up into factors
            have f_splits : Splits (RingHom.id ℝ) (f a)
              := splits_iff_card_roots.mpr f_degree_eq_roots_card

            -- the leading coefficient of f_a is 1
            have leading_eq_one : (f a).leadingCoeff = 1 := by
              rw [hf]
              apply Polynomial.leadingCoeff_quadratic
              linarith

            -- we split it up f_a(x) = (x - r1) * (x - r2)
            have splitted := Polynomial.eq_prod_roots_of_splits_id f_splits
            norm_num [roots, leading_eq_one] at splitted

            -- so f_a(-1) = (1 + r1) * (1 + r2)
            have f_neg_one_split : (f a).eval (-1) = (1 + r1) * (1 + r2) := by
              rw [splitted]
              norm_num
              ring

            -- which is part of the expression
            rw [←f_neg_one_split]

            -- but we also have f_a(-1) = 1 - 7 * a
            have f_neg_one_quadratic : (f a).eval (-1) = 1 - 7 * a := by
              rw [hf]
              norm_num
              ring

            rw [f_neg_one_quadratic]

            -- then we have f_a(1 - 6 * a) = (1 - 6 * a - r1) * (1 - 6 * a - r2)
            have f_sub_a_split : (f a).eval (1 - 6 * a) = (1 - 6 * a - r1) * (1 - 6 * a - r2) := by
                rw [splitted]
                norm_num

            -- which is also part of the expression
            rw [←f_sub_a_split]

            -- and we also have f_a(1 - 6 * a) = 1 - 7 * a
            have f_sub_a_quadratic : (f a).eval (1 - 6 * a) = 1 - 7 * a := by
              rw [hf]
              norm_num
              ring

            rw [f_sub_a_quadratic]

            -- so the denominators are positive
            rw [div_sub_div_same]

            -- we consider the case when denominators are equal to 0 seperately
            by_cases hh : 1 - 7 * a = 0
            · norm_num [hh]

            norm_num [hh]

            -- we factor the numerator
            have factor_numerator : (9 * a - 4 * a ^ 2 - (70 * a ^ 3 + 1))
              = (1 - 7 * a) * (10 * a ^ 2 + 2 * a - 1) := by
                ring
            rw [factor_numerator]

            -- simplify
            field_simp
            ring_nf

        rw [set_eq]

        -- now that the set is simplified we consider the definition of "least number"
        unfold IsLeast lowerBounds

        -- simplify
        simp only [_root_.div_eq_zero_iff, ne_eq, exists_and_right, Set.mem_setOf_eq,
          neg_eq_zero, OfNat.ofNat_ne_zero, or_self, false_and, or_false,
          forall_exists_index, and_imp]

        -- we prove both nessery properties
        split_ands
        -- we show that -89 / 81 is an achievable value
        -- it's achieved by a = -1 / 9
        · exists (-1 / 9)
          ring_nf
          norm_num

          -- we have f_(-1/9)(x) = (x - 1 / 3) * (x - 1 / 3)
          have f_eq : f (-(1 / 9)) = (X - C (1 / 3)) * (X - C (1 / 3)) := by
            rw [hf]
            norm_num
            apply Polynomial.funext
            intro x
            norm_num
            ring

          -- so 1 / 3 is a double root of the equation
          exists (1 / 3), (1 / 3)
          rw [f_eq, Polynomial.roots_mul]
          norm_num
          -- f_(-1/9) is non-zero
          · rw [←f_eq]
            exact f_ne_zero (-(1 / 9))
        -- then we'll show that -89 / 81 is a lower bound of all solutions
        · rintro A a x1 x2 root_eq (⟨aa, bb⟩ | ⟨rfl, aa⟩)
          -- in one case 1 - 7 * a ≠ 0
          -- f_a has at least one root
          · have has_root : ∃ x, x ∈ (f a).roots := by
              exists x1
              rw [root_eq]
              norm_num
            -- so a ∈ (-∞, -1/9] ∪ [0, ∞)
            rw [mem] at has_root
            -- which means a ≤ -1 / 9 ∨ 0 ≤ a
            simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici] at has_root

            -- we want to show -89 / 81 ≤ 10 * a ^ 2 + 2 * a - 1
            rw [aa]

            -- consider the values of a
            rcases has_root with h1 | h2
            -- when a ≤ -1 / 9, we see that the bound holds
            · nlinarith
            -- when 0 ≤ a, we see that the bound holds
            · nlinarith
          -- in the case that 1 - 7 * a = 0, we also had that x = 0
          -- and -89 / 81 ≤ 0
          · linarith