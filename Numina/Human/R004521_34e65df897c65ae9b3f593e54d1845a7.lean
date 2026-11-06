import Mathlib

/- Two sets S and T are order isomorphic if there exists some function f such that
  (i)  : T = { f(x) | x ∈ S}
  (ii) : ∀ x_1 x_2 ∈ S, x_1 < x_2 → f(x_1) < f(x_2) -/
def order_isomorphic (A : Type) (B : Type) [Preorder A] [Preorder B] (S : Set A) (T : Set B)
  := ∃ f : A → B, f '' S = T ∧ ∀ x1 ∈ S, ∀ x2 ∈ S, x1 < x2 → f x1 < f x2

/- 12. Let $S, T$ be two non-empty sets. If there exists a function $y=f(x)$ from $S$ to $T$ satisfying:
( $i$ ) $T=\{f(x) \mid x \in S\}$; (ii) $\forall x_{1}, x_{2} \in S$, when $x_{1} < x_{2}$, it always holds that $f (x_1) < f (x_2)$. Then these two sets are said to be "order-isomorphic". Prove: (1) A=(0,1),B=R are order-isomorphic; (2) Determine whether A=$Z$,B=$Q$ are order-isomorphic. If they are, provide a function expression; if not, explain the reason. -/
theorem algebra_278855 : order_isomorphic ℝ ℝ (Set.Ioo 0 1) Set.univ ∧ ¬(order_isomorphic ℤ ℚ Set.univ Set.univ)
  := by
    -- prove (1) and (2) separately
    split_ands
    -- we'll prove that they are order-isomorphic
    -- we provide a working function:
    -- tan ((x - 1 / 2) * π)
    · exists fun x => Real.tan ((x - 1 / 2) * Real.pi)
      -- we prove each property separately
      split_ands
      -- We'll prove that it's range is all real numbers
      -- it's a composition of functions
      · convert_to Real.tan ∘ (· * Real.pi) ∘ (· - 1 / 2) '' Set.Ioo 0 1 = Set.univ
        simp only [Set.image_comp]
        -- we know the range of subtraction
        rw [Set.image_sub_const_Ioo]
        -- we know the range of multiplication
        rw [Set.image_mul_right_Ioo _ _ (by positivity)]

        -- We know that tan is surjective on (-π / 2, π / 2)
        have surj := Real.image_tan_Ioo

        -- normalize
        ring_nf at surj ⊢
        -- then we see that it was as wanted
        exact surj
      -- it preserves orders
      · intro x1 h1 x2 h2 lee

        -- we have that x_1 is positive, and x_2 is less than 1
        norm_num at h1
        norm_num at h2
        have x1_pos : 0 < x1 := by tauto
        have x2_lt : x2 < 1 := by tauto

        -- then we're in the range of tan which preserves orders
        apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        -- we have -(π / 2) < (x_1 - 1 / 2) * π
        · ring_nf
          suffices : 0 < Real.pi * x1
          · linarith
          positivity
        -- and (x_2 - 1 / 2) * π < π / 2
        · ring_nf
          suffices : x2 * Real.pi < 1 * Real.pi
          · linarith

          exact (mul_lt_mul_iff_of_pos_right (by positivity)).mpr (by linarith)

        -- and the arguments were ordered
        -- i.e. (x_1 - 1 / 2) * π < (x_2 - 1 / 2) * π
        · exact (mul_lt_mul_iff_of_pos_right (by positivity)).mpr (by linarith)
    -- assume they are order preserving
    · by_contra has
      -- so we have an f : ℤ → ℚ which is surjective and preserves ordering
      obtain ⟨f, surj, all⟩ := has
      norm_num at all
      norm_num at surj
      have f_surj : f.Surjective := Set.range_eq_univ.mp surj

      -- let a be f(1), and b be f(2)
      let a := f 1
      let b := f 2

      -- then a < b
      have a_lt_b : a < b := by
        apply all
        omega

      -- let c be the average of a and b
      let c := (a + b) / 2

      -- then a < c
      have gtt : a < c := by
        norm_num [c]
        linarith
      -- and c < b
      have ltt : c < b := by
        norm_num [c]
        linarith

      -- because f is surjective, we have some x such that f(x) = c
      obtain ⟨x, xh⟩ : ∃ x, f x = c := f_surj c

      -- so a < f x < b
      rw [←xh] at gtt ltt

      -- but if f x < f y, then x < y
      have other : ∀ {x y}, f x < f y → x < y := by
        intro x y hh
        -- x is not y
        have x_ne_y : x ≠ y := by
          by_contra x_eq_y
          rw [x_eq_y] at hh
          linarith

        -- assume that y < x
        by_contra inv
        have y_lt_x : y < x := by omega

        -- then f y < f x
        have app := all y x y_lt_x

        -- but that's impossible
        linarith

      -- so 1 < x < 2
      have one_lt_x := other gtt
      have x_lt_two := other ltt

      -- but that's impossible, because x is an integer
      omega