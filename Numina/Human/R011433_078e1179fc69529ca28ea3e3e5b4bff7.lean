import Mathlib

set_option maxHeartbeats 400000

/- Example 14 Given real numbers $a, b, c, d, e$ satisfy $3a + 2b - c + 4d + \sqrt{133}e = \sqrt{133}, 2a^2 + 3b^2 + 3c^2 + d^2 + 6e^2 = 60$, try to find when $e$ takes its extreme values, and what are the maximum and minimum values respectively. -/
theorem algebra_265259:
    let system: ℝ → ℝ → ℝ → ℝ → ℝ → Prop := fun a b c d e =>
      3 * a + 2 * b - c + 4 * d + Real.sqrt 133 * e = Real.sqrt 133 ∧
      2 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + d ^ 2 + 6 * e ^ 2 = 60
    let S: Set ℝ :=
      { e: ℝ | ∃ (a b c d: ℝ), system a b c d e }
    IsGreatest S ((1 + √19) / 2) ∧ IsLeast S ((1 - √19) / 2) ∧
    (∀ a b c d e (Hs: system a b c d e),
      (e = (1 - √19) / 2) ↔
      (a = 3 * d / 8 ∧ b = d / 6 ∧ c = - d / 12 ∧ d = 12 * (√133 + 19 * √7) / 133)) ∧
    (∀ a b c d e (Hs: system a b c d e),
      (e = (1 + √19) / 2) ↔
      (a = 3 * d / 8 ∧ b = d / 6 ∧ c = - d / 12 ∧ d = 12 * (√133 - 19 * √7) / 133)) := by

  intros system S

  -- the standard Cauchy-Schwarz inequality for `Fintype` and real numbers,
  -- easy consequence of lemma from the library
  have fintype_Cauchy_Schwarz_inequality {ι: Type} [inst: Fintype ι] (f g: ι → ℝ):
      (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq

  -- criterion for the equality in the Cauchy-Schwarz inequality
  -- derived from another lemma in the library
  -- this time the proof is much longer
  -- because the lamma is about inner product spaces etc.
  have fin_Cauchy_Schwarz_equality_criterion {n} (f g: Fin n → ℝ) (Hf: f ≠ 0) (Hg: g ≠ 0):
      abs (∑ i, f i * g i) = √(∑ i, f i ^ 2) * √(∑ i, g i ^ 2) ↔
      (∃ (k: ℝ), ¬ k = 0 ∧ ∀ i, g i = k * f i) := by
    -- let's make n-dimensional vectors of Euclidean space
    -- from the parameters with type `Fin n → ℝ`: `f` and `g`
    set x: EuclideanSpace ℝ (Fin n) := (WithLp.equiv _ _).symm f
    set y: EuclideanSpace ℝ (Fin n) := (WithLp.equiv _ _).symm g
    -- we use the library lemma with necessary parameters
    have H := norm_inner_eq_norm_iff (𝕜 := ℝ) (x := x) (y := y) Hf Hg
    -- let's unfold the meaning of `x` and `y`
    simp [x, y] at H

    -- this lemma will prove that the norm of vector correspoding to `t: Fin n → ℝ`
    -- is the standard sum of squared values `f i`
    have Ht (t: Fin n → ℝ): ‖(WithLp.equiv 2 (Fin n → ℝ)).symm t‖ = √(∑ i, (t i) ^ 2) := by
      -- few unfoldings with simplification at the end
      -- to change the goal into much simpler form
      unfold WithLp.equiv Equiv.refl norm PiLp.instNorm
      simp
      -- this tiny, but useful result follows from the fact that
      -- the sum of any number of squares is nonnegative
      have H0: 0 ≤ ∑ i, t i ^ 2 := by
        apply Finset.sum_nonneg
        intros i
        simp
        apply sq_nonneg (t i)
      -- let's replace that power to `2⁻¹` with standard square root
      refine ((Real.rpow_inv_eq H0 (by apply Real.sqrt_nonneg) (by norm_num)).mpr ?_)
      rw [← Real.rpow_div_two_eq_sqrt 2 H0]
      simp

    -- now we can use the lemma `Ht` to simplify the hypothesis `H`
    simp_rw [Ht] at H
    -- and then simplify the goal
    rw [H]
    -- now simplify the goal even more using this lemma
    have Ht0 (k: ℝ) (t: Fin n → ℝ): k • (WithLp.equiv 2 (Fin n → ℝ)).symm t = fun x => k * t x := by
      congr
    simp_rw [Ht0]
    -- the goal is double implication, let's destruct it into two parts
    constructor <;> intro H0
    . -- destruct hypothesis `H0` to get the number and some useful facts
      obtain ⟨k, Hk, H1⟩ := H0
      -- move from equality of functions to their pointwise equality
      rw [funext_iff] at H1
      -- use the real number and proofs we got by destruting `H0`
      use k
      exact ⟨Hk, H1⟩
    . -- same strategy - destruct, use the value, then `funext_iff`,
      -- and finally use proof we got from destructed hypothesis
      obtain ⟨k, Hk, H1⟩ := H0
      use k
      rw [funext_iff]
      exact ⟨Hk, H1⟩

  -- to use these two theorems (`fintype_Cauchy_Schwarz_inequality` and
  -- `fin_Cauchy_Schwarz_equality_criterion`) we need two functions of type `fin n → ℝ`.
  -- in this case `n` is equal to `4`.

  -- these specific definitions of `f` and `g` will be useful later

  -- `f` will be used just like specific four numbers
  let f: Fin 4 → ℝ := fun i =>
    match i with
    | 0 => 3 / √2
    | 1 => 2 / √3
    | 2 => - 1 / √3
    | 3 => 4

  -- `g` will depend on values of `a`, `b`, `c` and `d`
  let g a b c d: Fin 4 → ℝ := fun i =>
    match i with
    | 0 => √2 * a
    | 1 => √3 * b
    | 2 => √3 * c
    | 3 => d

  -- specialize the `fintype_Cauchy_Schwarz_inequality` and `fin_Cauchy_Schwarz_equality_criterion`
  -- in the second case (theorem `equality_criterion`) we also provide the proof that `f ≠ 0`
  have inequality a b c d := fintype_Cauchy_Schwarz_inequality f (g a b c d)
  have equality_criterion a b c d := fin_Cauchy_Schwarz_equality_criterion f (g a b c d)
    (by simp only [f]; intro Hf; rw [funext_iff] at Hf; have Hf' := Hf 0; simp at Hf')

  -- the first auxiliary result
  have aux_1 a b c d: (∑ i, f i * g a b c d i) = 3 * a + 2 * b - c + 4 * d := by
    -- rewrite using useful theorem, that `unfolds` the sum sign and replace it by four summands
    rw [Fin.sum_univ_four]
    -- unfold `f` and `g` and then simplify using few tactics
    unfold f g
    simp
    ring_nf
    norm_num

  -- the second auxiliary result, the same strategy as in the first
  have aux_2: (∑ i : Fin 4, f i ^ 2) = 133 / 6 := by
    rw [Fin.sum_univ_four]
    unfold f
    simp
    ring_nf
    norm_num

  -- the third auxiliary result. the same approach as in the first two
  have aux_3 a b c d: (∑ i, g a b c d i ^ 2) = 2 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + d ^ 2 := by
    rw [Fin.sum_univ_four]
    unfold g
    simp
    ring_nf
    norm_num
    ring

  -- rewrite in hypotheses `inequality` and `equality_criterion`
  -- using these three lemmas and then clear them away from the proof state
  simp_rw [aux_1, aux_2, aux_3] at inequality
  simp_rw [aux_1, aux_2, aux_3] at equality_criterion
  clear aux_1 aux_2 aux_3

  -- let's prove that the set of all possible values of `e`
  -- is a subset of some specific interval
  -- (from minimum value of `e` to maximum value of `e`)
  have S_is_subset_of_interval e (Hx: e ∈ S): e ∈ Set.Icc ((1 - √19) / 2) ((1 + √19) / 2) := by
    -- unfold, simplify and destruct
    unfold S system at *
    simp at *
    obtain ⟨a, b, c, d, eq_1, eq_2⟩ := Hx
    -- move summand with variable `e` in it to the right side of equation `eq_1`
    rw [<- eq_sub_iff_add_eq] at eq_1 eq_2
    -- now use the result `inequality` with specific arguments
    have ineq := inequality a b c d
    -- rewrite at hypothesis `ineq`
    -- (lemma `tsub_nonpos` here is used to change nonstrict inequality of two values
    -- to nonpositivity of the difference of those two values)
    rw [eq_1, eq_2, <- tsub_nonpos] at ineq
    -- some simplification (tactics `ring_nf`, `field_simp`)
    ring_nf at ineq
    field_simp at ineq
    ring_nf at ineq
    -- change the left side of the inequality into
    -- more useful form for solving it
    rw [show -1197 - e * 266 + e ^ 2 * 266 = 266 * ((e - 1 / 2) ^ 2 - (√19 / 2) ^ 2)
      by ring_nf; field_simp; ring] at ineq
    -- remove that multiplication by `266` (a positive number) from inequality
    rw [mul_nonpos_iff] at ineq
    norm_num at ineq
    -- more rewrites to get closer to the goal
    rw [sq_le_sq, abs_of_pos (a := √19 / 2) (by norm_num), abs_le] at ineq
    -- destruct the hypothesis `ineq` (in its current state) into two parts
    -- then destruct goal and use tactic `linarith`
    -- (sadly the tactic can't deal with conjunctions, so we do that for it)
    obtain ⟨ineq1, ineq2⟩ := ineq
    constructor <;> linarith

  -- let's prove: that for all the solutions of the system,
  -- if `e` is one of two given values, then the values of
  -- `a`, `b`, `c`, `d` are uniquely determined from `e`
  have consequence_of_extremum a b c d e (Hs: system a b c d e) (He: e = (1 - √19) / 2 ∨ e = (1 + √19) / 2):
      (a = 3 * d / 8 ∧ b = d / 6 ∧ c = - d / 12 ∧ d = 24 * (1 - e) / √133) := by
    -- first we are going to get the result that is useful
    -- for our lemma `equality_criterion`

    -- auxiliary lemma that we are ggoing to use
    -- the equality that holds for both of these values of `e`
    have eq: (√133 - √133 * e) ^ 2 = 133 / 6 * (60 - 6 * e ^ 2) := by
      -- destruct, substitute value of `e` and simplify
      obtain He | He := He
      . subst e
        ring_nf
        field_simp
        ring_nf
      . subst e
        ring_nf
        field_simp
        ring_nf

    -- unfold the definition of `system`, then destruct it in two parts
    -- each are the corresponding equations of the system
    unfold system at Hs
    obtain ⟨eq_1, eq_2⟩ := Hs

    -- move values around a bit in both `eq_1` and `eq_2`
    rw [<- eq_sub_iff_add_eq] at eq_1 eq_2
    -- use `eq_1` and `eq_2` to rewrite in `eq`
    rw [<- eq_1, <- eq_2] at eq
    -- with the next four rewrites get the `eq` into form,
    -- appropriate for the lemma `equality_criterion`
    rw [<- Real.sq_sqrt (x := 133 / 6 * (2 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + d ^ 2)) (by nlinarith)] at eq
    rw [sq_eq_sq_iff_abs_eq_abs] at eq
    rw [abs_of_nonneg (a := √(133 / 6 * (2 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + d ^ 2))) (by apply Real.sqrt_nonneg)] at eq
    rw [Real.sqrt_mul (by norm_num)] at eq

    -- now, to finally use the lemma `equality_criterion`,
    -- we look at the two possibilities:
    -- either `g a b c d = 0` (which for type `Fin 4 → ℝ` means function,
    -- that's zero no matter the input), or `g a b c d ≠ 0` (the opposite -
    -- meaning that for some possible input the result isn't zero)
    obtain Hv | Hv := eq_or_ne (g a b c d) 0

    . -- unfold the definition of `g`
      simp [g] at Hv
      -- rewrite using `funext_iff` to get
      -- from function equality to pointwise equality
      rw [funext_iff] at Hv
      -- we prove that `a`, `b`, `c`, `d` all are zeroes, then substitute
      have Ha: a = 0 := by have Ha := Hv 0; simp at Ha; exact Ha
      have Hb: b = 0 := by have Hb := Hv 1; simp at Hb; exact Hb
      have Hc: c = 0 := by have Hc := Hv 2; simp at Hc; exact Hc
      have Hd: d = 0 := by have Hd := Hv 3; simp at Hd; exact Hd
      subst a b c d
      -- we have two cases for value of `e`, in each we reach a contradiction
      obtain He | He := He
      . -- substitution, simplifications at `eq_1` and
        -- finally use of the tactic `linarith`, which solves the goal,
        -- because `eq_1` isn't possible
        subst e
        norm_num at eq_1
        field_simp at eq_1
        ring_nf at eq_1
        have Hsqrt_133: 0 < √133 := by norm_num
        have Hsqrt_19: 0 < √19 := by norm_num
        nlinarith
      . -- the same approach as in the first case
        subst e
        norm_num at eq_1
        field_simp at eq_1
        ring_nf at eq_1
        have Hsqrt_133: 0 < √133 := by norm_num
        have Hsqrt_19: 0 < √19 := by norm_num
        nlinarith

    . -- we are using the lemma `equality_criterion` on hypothesis `eq`, finally
      rw [equality_criterion a b c d Hv] at eq
      -- now, when hypothesis `eq` is transformed in statement about existence
      -- we, of course, destruct it, getting a value `k` and two statements
      obtain ⟨k, Hk, Hi⟩ := eq
      -- unfold definitions of `f` and `g` at hypothesis `Hi`
      unfold f g at Hi

      -- first we calculate the specific value of that variable `k`
      have H3 := Hi 3
      simp at H3
      have Hkd: k = d / 4 := by linarith

      -- then we use it and prove the first three parts of the goal
      -- by using hypothesis `Hi` with the values `0`, `1` and `2`
      -- (for `a`, `b` and `c`)
      rw [Hkd] at Hi
      have Ha: a = 3 * d / 8 := by
        have Hi0 := Hi 0
        simp at Hi0
        field_simp at Hi0
        ring_nf at Hi0
        norm_num at Hi0
        linarith
      have Hb: b = d / 6 := by
        have Hi1 := Hi 1
        simp at Hi1
        field_simp at Hi1
        ring_nf at Hi1
        norm_num at Hi1
        linarith
      have Hc: c = - d / 12 := by
        have Hi2 := Hi 2
        simp at Hi2
        field_simp at Hi2
        ring_nf at Hi2
        norm_num at Hi2
        linarith
      refine ⟨Ha, Hb, Hc, ?_⟩

      -- now, to prove the final part of the goal:
      -- rewrite the expressions for `a`, `b` and `c` in hypothesis `eq_1`
      -- (to get an equality with variable `d` on the right side and `e` on the left side)
      -- and then do necessary transformations of this identity
      rw [Ha, Hb, Hc] at eq_1
      ring_nf at eq_1
      rw [<- eq_div_iff (by norm_num)] at eq_1

      -- then rewrite in the goal using it (the hypothesis `eq_1`) and
      -- simplify until the goal is solved
      rw [eq_1]
      field_simp
      ring_nf
      norm_num
      ring

  -- let's prove criterion for the least value of `e` that's possible
  have criterion_for_the_least_e a b c d e (Hs: system a b c d e):
      (e = (1 - √19) / 2) ↔
      (a = 3 * d / 8 ∧ b = d / 6 ∧ c = - d / 12 ∧ d = 12 * (√133 + 19 * √7) / 133) := by
    constructor <;> intro H
    . -- (direction from left to right)
      -- we use the lemma `consequence_of_extremum`
      have H0 := consequence_of_extremum a b c d e Hs (Or.inl H)
      -- destructing H0, we can prove the first three parts of the goal
      obtain ⟨Ha, Hb, Hc, Hd⟩ := H0
      refine ⟨Ha, Hb, Hc, ?_⟩
      -- now some rewwriting and simplification
      rw [Hd, H]
      field_simp
      ring_nf
      norm_num
      -- simplifications of square roots
      rw [<- Real.sqrt_mul (by norm_num)]
      rw [show (133: ℝ) * 7 = 19 * 7 ^ 2 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
      ring
    . -- (direction from right to left)
      -- we use the first equation of the system
      have eq_1 := Hs.1
      -- destruct H and use values of `a`, `b`, `c` and `d`
      -- to rewrite in the first equation
      obtain ⟨Ha, Hb, Hc, Hd⟩ := H
      rw [Ha, Hb, Hc, Hd] at eq_1
      -- now let's simplify the current form of the equation `eq_1`
      ring_nf at eq_1
      field_simp at eq_1
      rw [<- sub_eq_zero] at eq_1
      ring_nf at eq_1
      have H0: e = (√133 - √7 * 19) / (2 * √133) := by field_simp; linarith
      rw [H0]
      field_simp
      ring_nf
      rw [<- Real.sqrt_mul (by norm_num)]
      rw [show (133: ℝ) * 19 = 7 * 19 ^ 2 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
      ring

  -- criterion for the greatest value of `e` that's possible, too.
  -- the approach is the same as with the previous theorem
  have criterion_for_the_greatest_e a b c d e (Hs: system a b c d e):
      (e = (1 + √19) / 2) ↔
      (a = 3 * d / 8 ∧ b = d / 6 ∧ c = - d / 12 ∧ d = 12 * (√133 - 19 * √7) / 133) := by
    constructor <;> intro H
    . have H0 := consequence_of_extremum a b c d e Hs (Or.inr H)
      obtain ⟨Ha, Hb, Hc, Hd⟩ := H0
      refine ⟨Ha, Hb, Hc, ?_⟩
      rw [Hd, H]
      field_simp
      ring_nf
      norm_num
      rw [<- Real.sqrt_mul (by norm_num)]
      rw [show (133: ℝ) * 7 = 19 * 7 ^ 2 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
      ring
    . have eq_1 := Hs.1
      obtain ⟨Ha, Hb, Hc, Hd⟩ := H
      rw [Ha, Hb, Hc, Hd] at eq_1
      ring_nf at eq_1
      field_simp at eq_1
      rw [<- sub_eq_zero] at eq_1
      ring_nf at eq_1
      have H0: e = (√133 + √7 * 19) / (2 * √133) := by field_simp; linarith
      rw [H0]
      field_simp
      ring_nf
      rw [<- Real.sqrt_mul (by norm_num)]
      rw [show (133: ℝ) * 19 = 7 * 19 ^ 2 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
      ring

  -- now it's time to prove all four parts of the goal
  refine ⟨?_, ?_, ?_, ?_⟩
  . -- the part about the greatest possible value of `e`
    simp only [IsGreatest]
    constructor
    . -- prove that the specific value (`(1 + √19) / 2`) belongs
      -- to the set of possible values of `e`
      unfold S system
      simp only [Set.mem_setOf_eq]
      set t := 1 / 133 * (√133 - 19 * √7)
      -- one sure way to prove the goal is to give specific values
      -- of variables `a`, `b`, `c`, `d`, that together with
      -- given value of `e` solves the system of equations
      -- (or - makes the predicate `system` to be `True`)
      use 9 / 2 * t, 2 * t, - t, 12 * t
      rw [show 3 * (9 / 2 * t) + 2 * (2 * t) - -t + 4 * (12 * t) = 133 / 2 * t by ring]
      rw [show 2 * (9 / 2 * t) ^ 2 + 3 * (2 * t) ^ 2 + 3 * (-t) ^ 2 + (12 * t) ^ 2 = 399 / 2 * t ^ 2 by ring]
      field_simp
      ring_nf
      norm_num
      ring_nf
      rw [show (133: ℝ) = 19 * 7 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      constructor
      . ring_nf
        norm_num
        ring
      . rw [<- sub_eq_zero]
        ring_nf
        norm_num
        ring
    . -- prove that the value (`(1 + √19) / 2`) is
      -- the maximum possible value of `e`
      simp only [upperBounds]
      simp only [Set.mem_setOf_eq]
      intros e He
      -- now we use the fact that S is subset of
      -- the interval `((1 - √19) / 2, (1 + √19) / 2)`
      apply S_is_subset_of_interval at He
      simp only [Set.mem_Icc] at He
      exact He.2
  . -- the part about the lowest possible value of `e`
    -- we do almost the same as in the previous part about
    -- the biggest possible value of `e`
    simp only [IsLeast]
    constructor
    . unfold S system
      simp only [Set.mem_setOf_eq]
      set t := 1 / 133 * (√133 + 19 * √7)
      use 9 / 2 * t, 2 * t, - t, 12 * t
      rw [show 3 * (9 / 2 * t) + 2 * (2 * t) - -t + 4 * (12 * t) = 133 / 2 * t by ring]
      rw [show 2 * (9 / 2 * t) ^ 2 + 3 * (2 * t) ^ 2 + 3 * (-t) ^ 2 + (12 * t) ^ 2 = 399 / 2 * t ^ 2 by ring]
      field_simp
      ring_nf
      norm_num
      field_simp
      norm_num
      ring_nf
      rw [show (133: ℝ) = 19 * 7 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      constructor
      . ring_nf
        norm_num
        ring
      . rw [<- sub_eq_zero]
        ring_nf
        norm_num
        ring
    . simp only [lowerBounds]
      simp only [Set.mem_setOf_eq]
      intros e He
      apply S_is_subset_of_interval at He
      simp only [Set.mem_Icc] at He
      exact He.1
  . -- this and the last part is easy to do
    -- as they are exactly the previously proven lemmas
    intros a b c d e Hs
    exact criterion_for_the_least_e a b c d e Hs
  . intros a b c d e Hs
    exact criterion_for_the_greatest_e a b c d e Hs

-- QED