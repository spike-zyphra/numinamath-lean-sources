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

/- The function (x + x⁻¹) ^ 3 is convex on the positive real numbers. -/
lemma Convex_Real_add_inv_pow_three : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => (x + x⁻¹) ^ 3)
  := by
    -- the positive real numbers is a subset of the non-zero real numbers
    have subs : (Set.Ioi (0 : ℝ)) ⊆ {0}ᶜ
      := Set.subset_compl_singleton_iff.mpr Set.not_mem_Ioi_self

    -- x + x⁻¹ is continuous on the positive real numbers
    have add_inv_cont : ContinuousOn (fun x : ℝ => x + x⁻¹) (Set.Ioi 0)
      := (continuousOn_id' (Set.Ioi 0)).add (continuousOn_inv₀.mono subs)

    -- the image of x + x⁻¹ on the positive real numbers is positive
    have subs' : (fun x : ℝ => x + x⁻¹) '' Set.Ioi 0 ⊆ Set.Ici 0 := by
      intro x
      norm_num
      rintro y yh rfl
      positivity

    -- x ^ 3 is monotone on positive real numbers
    have mono_pow : MonotoneOn (fun x : ℝ => x ^ 3) (Set.Ici 0) := by
      convert_to MonotoneOn (fun x : ℝ => x ^ ((3 : ℕ) : ℝ)) (Set.Ici 0)
      ext i
      exact (Real.rpow_natCast i 3).symm
      exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by norm_num)

    -- then we have that ((· ^ 3) ∘ (fun x => x + x⁻¹)) is convex on the positive real numbers
    have convex_k : ConvexOn ℝ (Set.Ioi 0) ((· ^ 3) ∘ (fun x : ℝ => x + x⁻¹)) := by
      -- the composition of function is convex
      apply ConvexOn.comp
      -- because x ^ 3 is convex on the image of x + x⁻¹
      · refine ConvexOn.subset (convexOn_pow 3) subs' ?_
        · exact Real.convex_iff_isPreconnected.mpr
            (isConnected_Ioi.image (fun x : ℝ => x + x⁻¹) add_inv_cont).isPreconnected
      -- x + x⁻¹ is convex on the positive real number
      · exact (convexOn_id (convex_Ioi 0)).add Convex_Real_inv
      -- x + x⁻¹ is monotone
      · exact mono_pow.mono subs'

    -- which is what we wanted
    exact convex_k

/- 4. Find the largest constant $C$ such that

$$

\sum_{i=1}^{4}\left(x_{i}+\frac{1}{x_{i}}\right)^{3} \geq C

$$

for all positive real numbers $x_{1}, \cdots, x_{4}$ such that

$$

x_{1}^{3}+x_{3}^{3}+3 x_{1} x_{3}=x_{2}+x_{4}=1 \text {. }

$$
 -/
theorem inequalities_287091
  : IsGreatest {C | ∀ x : Fin 4 → ℝ,
      (∀ i, 0 < x i) → (x 0) ^ 3 + (x 2) ^ 3 + 3 * (x 0) * (x 2) = 1 → (x 1) + (x 3) = 1 → C ≤ ∑ i, (x i + (x i)⁻¹) ^ 3}
        (125 / 2)
  := by
    unfold IsGreatest upperBounds

    -- prove both parts separately
    split_ands
    -- we'll prove it's an upper bound
    · simp only [Set.mem_setOf]
      intro x x_pos eq_1 eq_2

      -- move terms to LHS
      have eq_0 : x 0 ^ 3 + x 2 ^ 3 + 3 * x 0 * x 2 - 1 = 0 := by linarith

      -- factor the equality
      have factored : x 0 ^ 3 + x 2 ^ 3 + 3 * x 0 * x 2 - 1
        = (x 0 + x 2 - 1) * ((x 0 - x 2) ^ 2 + (x 0 + 1) * (x 2 + 1)) := by ring

      rw [factored] at eq_0

      -- then one of the factors is 0
      norm_num at eq_0

      -- note that every x value is positive
      have x_0_pos : 0 < x 0 := x_pos 0
      have x_1_pos : 0 < x 1 := x_pos 1
      have x_2_pos : 0 < x 2 := x_pos 2
      have x_3_pos : 0 < x 3 := x_pos 3

      -- consider each case
      rcases eq_0 with simple | complicated
      -- in one case x 0 + x 2 = 1
      · have eq_3 : x 0 + x 2 = 1 := by linarith

        -- it's sufficient to show that, given x + y = 1 where 0 < x and 0 < y, then
        -- 125 / 4 ≤ (x + x⁻¹) ^ 3 + (y + y⁻¹) ^ 3
        suffices : ∀ {x y : ℝ}, x + y = 1 → 0 < x → 0 < y → 125 / 4 ≤ (x + x⁻¹) ^ 3 + (y + y⁻¹) ^ 3
        -- expand sum
        · rw [Fin.sum_univ_four]
          -- group symmetric terms
          convert_to 125 / 4 + 125 / 4
            ≤ ((x 0 + (x 0)⁻¹) ^ 3 + (x 2 + (x 2)⁻¹) ^ 3)
            + ((x 1 + (x 1)⁻¹) ^ 3 + (x 3 + (x 3)⁻¹) ^ 3)
          · ring
          · ring

          -- bound term-wise
          gcongr
          · exact this eq_3 x_0_pos x_2_pos
          · exact this eq_2 x_1_pos x_3_pos

        intro x y eq x_pos y_pos

        have y_eq : y = 1 - x := by linarith
        rw [y_eq] at y_pos ⊢

        -- let (x + x⁻¹) ^ 3
        let f := (fun x : ℝ => (x + x⁻¹) ^ 3)

        -- then we are to show 125 / 4 ≤ f x + f (1 - x)
        convert_to 125 / 4 ≤ f x + f (1 - x)

        -- 1 / 2 is positive
        have half_pos : 0 < (1 / 2 : ℝ) := by linarith

        -- f is convex on positive arguments
        have f_convex : ConvexOn ℝ (Set.Ioi 0) f := Convex_Real_add_inv_pow_three

        -- then we have that f (1 / 2 * x + 1 / 2 * (1 - x)) ≤ 1 / 2 * f x + 1 / 2 * f (1 - x)
        have convex_add := (convexOn_iff_forall_pos.mp f_convex).2 x_pos y_pos half_pos half_pos (by norm_num)
        norm_num at convex_add

        -- two is positive
        have two_pos : 0 < (2 : ℝ) := by linarith

        -- so multiply both sides by 2
        replace convex_add := (mul_le_mul_left two_pos).mpr convex_add

        -- then the RHS is equal to f x + f (1 - x)
        have rhs_eq : 2 * (1 / 2 * f x + 1 / 2 * f (1 - x)) = f x + f (1 - x) := by ring
        rw [rhs_eq] at convex_add

        -- then the RHS of the inequality is in the wanted form
        convert convex_add using 1
        -- and the LHS too
        · ring_nf

      -- then we have that (x_0 - x_2) ^ 2 + (x_0 + 1) * (x_2 + 1) = 0
      -- but the right term is positive
      · have right_pos : 0 ≤ (x 0 + 1) * (x 2 + 1) := by positivity
        -- and the left term too
        have left_pos : 0 ≤ (x 0 - x 2) ^ 2 := by positivity
        -- so the right term is 0
        have right_eq_zero : (x 0 + 1) * (x 2 + 1) = 0 := by linarith

        -- which means that x_0 = -1 or x_2 = -1
        norm_num at right_eq_zero

        -- but both cases are impossible, because x_0 and x_2 are positive
        rcases right_eq_zero <;> linarith

    -- then we prove that it's achievable
    -- we can achieve the bound using x_0 = x_1 = x_2 = x_3 = 1 / 2
    · simp only [Set.mem_setOf]
      intro C x_eq
      have app := x_eq (fun i => (1 / 2))

      -- simplify
      norm_num at app
      -- then we have that C ≤ 125 / 2
      tauto