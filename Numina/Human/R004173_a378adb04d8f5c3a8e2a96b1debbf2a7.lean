import Mathlib

/- The reciprocal is convex on the positive real numbers. -/
lemma Convex_Real_inv : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x⁻¹) := by
    have subs : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ
      := Set.subset_compl_singleton_iff.mpr Set.not_mem_Ioi_self

    -- we prove it using continuity and derivative properties
    refine convexOn_of_deriv2_nonneg (convex_Ioi 0) ?_ ?_ ?_ ?_
    -- reciprocal is continuous on positive real numbers
    · exact continuousOn_inv₀.mono subs
    -- reciprocal is differentiable on positive real numbers
    · norm_num
      apply differentiableOn_id.inv
      exact fun x a => subs a
    -- the first derivative of the reciprocal is differentiable on positive real numbers
    · norm_num
      apply (differentiableOn_pow 2).inv
      norm_num
      exact fun x a => subs a
    -- the second derivative of the reciprocal is positive on positive real numbers
    · norm_num
      intro x xh
      positivity

/- The image of the power on the positive real numbers is all the positive numbers. -/
lemma Real_rpow_pos {r : ℝ} (hr : r ≠ 0) :
  (fun x : ℝ => x ^ r) '' Set.Ioi 0 = Set.Ioi 0 := by
    -- we'll show that every element which is in one is in the other
    ext x

    -- simplify
    norm_num

    -- we show both directions separately
    constructor
    -- given 0 < x, then 0 < x ^ r
    · rintro ⟨x, h1, rfl⟩
      positivity
    -- given 0 < x, then 0 < x ^ (1 / r)
    -- and (x ^ (1 / r)) ^ r = x
    · intro pos
      exists x ^ (1 / r)
      split_ands
      · positivity
      · simp only [one_div]
        exact Real.rpow_inv_rpow (by positivity) (by tauto)

/- 4. Let $a, b, c > 0$, and satisfy $a+b+c=1$. Prove:

$$

\frac{a}{\sqrt[3]{a+2 b}}+\frac{b}{\sqrt[3]{b+2 c}}+\frac{c}{\sqrt[3]{c+2 a}} \geqslant 1 .

$$
 -/
theorem inequalities_240754 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    1 ≤ a / (a + 2 * b) ^ ((1 : ℝ) / 3) +
        b / (b + 2 * c) ^ ((1 : ℝ) / 3) +
        c / (c + 2 * a) ^ ((1 : ℝ) / 3)
  := by

    -- The image of "1 / 3"rd power on the positive real numbers is all the positive numbers
    have pow_image : (fun x : ℝ => x ^ (1 / 3 : ℝ)) '' Set.Ioi 0 = Set.Ioi 0
      := Real_rpow_pos (by linarith)

    -- the function (x ^ (1 / 3)) ^ (-1) is convex on the positive numbers
    have pow_convex : ConvexOn ℝ (Set.Ioi 0) (Inv.inv ∘ (fun x : ℝ => x ^ ((1 / 3 : ℝ))))
      := by
        -- it's a composition of functions
        apply ConvexOn.comp_concaveOn
        -- the inverse function is convex
        · rw [pow_image]
          exact Convex_Real_inv
        -- x ^ (1 / 3) is concave
        · have concave_nonneg : ConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ (1 / 3 : ℝ)
            := Real.concaveOn_rpow (by linarith) (by linarith)
          exact concave_nonneg.subset (Set.Ioi_subset_Ici_self) (convex_Ioi 0)
        -- and x ^ (-1) is antitone
        · rw [pow_image]
          convert_to AntitoneOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioi 0)
          · ext x
            exact (Real.rpow_neg_one x).symm
          exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)

    -- so we will use Jensen's inequality for our bound

    -- let the weights be a b c
    let w := ![a, b, c]

    -- each weight is non-negative
    have w_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      norm_num [w]
      intro i
      fin_cases i <;> (norm_num; linarith)

    -- and the weights sum to 1
    have w_sum : ∑ i ∈ Finset.univ, w i = 1 := by
      norm_num [Fin.sum_univ_three, w, h]

    -- the terms will be a + 2 * b, b + 2 * c and c + 2 * a
    let p := ![a + 2 * b, b + 2 * c, c + 2 * a]

    -- each term is positive
    have p_mem : ∀ i ∈ Finset.univ, p i ∈ Set.Ioi 0 := by
      norm_num [p]
      intro i
      fin_cases i
      all_goals
      · norm_num
        linarith

    -- apply Jensen's inequality
    have bound := pow_convex.map_sum_le w_nonneg w_sum p_mem

    -- simplify it
    norm_num at bound

    -- We can simplify part of the LHS to (a + b + c) ^ 2
    have lhs_eq : ∑ x : Fin (Nat.succ 0).succ.succ, w x * p x = (a + b + c) ^ 2 := by
      norm_num [Fin.sum_univ_three, w, p]
      ring

    -- so the LHS is equal to 1
    norm_num [lhs_eq, h] at bound

    -- so we have the bound
    convert bound
    -- normalize
    · norm_num [Fin.sum_univ_three, w, p]
      ring