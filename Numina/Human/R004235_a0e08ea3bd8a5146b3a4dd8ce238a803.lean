import Mathlib

/- Problem 1. We say that a quadruple of nonnegative real numbers $(a, b, c, d)$ is balanced if


$$

a+b+c+d=a^{2}+b^{2}+c^{2}+d^{2}

$$


Find all positive real numbers $x$ such that


$$

(x-a)(x-b)(x-c)(x-d) \geqslant 0

$$


for every balanced quadruple $(a, b, c, d)$.

(Ivan Novak) -/
theorem algebra_244075 (x : ℝ) (hx : x > 0) :
    (∀ a b c d : ℝ, a ≥ 0 → b ≥ 0 → c ≥ 0 → d ≥ 0 →
      (a + b + c + d = a^2 + b^2 + c^2 + d^2) →
        ((x - a) * (x - b) * (x - c) * (x - d) ≥ 0)) ↔
    x ≥ 3 / 2 := by
      -- use ≤ instead of ≥
      simp only [ge_iff_le]

      -- use < instead of >
      simp only [gt_iff_lt] at hx

      -- we show both direction seperately
      constructor
      · intro hh
        -- assume x is less than 3 / 2
        by_contra x_three_halves
        norm_num at x_three_halves

        -- consider  when x is at least 1
        by_cases 1 ≤ x
        -- then consider a = 3 / 2, b = c = d = 1 / 2
        · have app := hh (3 / 2) (1 / 2) (1 / 2) (1 / 2)
            (by positivity) (by positivity) (by positivity) (by positivity)
            (by ring)

          -- then the product is negative
          have prod_lt : (x - 3 / 2) * (x - 1 / 2) * (x - 1 / 2) * (x - 1 / 2) < 0 := by
            -- one factor is negative
            have pos : (x - 3 / 2) < 0 := by linarith
            -- the rest are positive
            have neg : 0 < (x - 1 / 2) := by linarith

            -- so product is negative
            have two_neg : (x - 3 / 2) * (x - 1 / 2) < 0 := mul_neg_of_neg_of_pos pos neg
            have three_pos : (x - 3 / 2) * (x - 1 / 2) * (x - 1 / 2) < 0
              := mul_neg_of_neg_of_pos two_neg neg
            exact mul_neg_of_neg_of_pos three_pos neg

          -- but the product should be positive, contradiction
          linarith
        -- so let x be less than 1
        -- then consider a = 1, b = c = d = 0
        · have app := hh 1 0 0 0
            (by positivity) (by positivity) (by positivity) (by positivity)
            (by ring)
          -- then the product becomes -x ^ 3 + x ^ 4
          ring_nf at app

          -- so we have that x ^ 3 ≤ x ^ 4
          simp only [le_neg_add_iff_add_le, add_zero] at app

          -- but x ^ 4 < x ^ 3
          have pow_lt : x ^ 4 < x ^ 3 := pow_lt_pow_right_of_lt_one₀ hx (by linarith) (by linarith)

          -- contradiction
          linarith

      -- then we show that 3 / 2 ≤ x works
      · intro xh a b c d ha hb hc hd hh

        -- let f_i be a, b, c and d
        let f := ![a, b, c, d]
        -- wlog, f is monotone, else we sort the values
        wlog hf : Monotone f generalizing a b c d
        -- every f value is non-negative
        · have f_pos : ∀ i, 0 ≤ f i := by
            intro i
            fin_cases i <;> norm_num [f, ha, hb, hc, hd]

          -- combine terms into sum
          have sum_eq : (f ∘ (Tuple.sort f)) 0 + (f ∘ (Tuple.sort f)) 1 + (f ∘ (Tuple.sort f)) 2 + (f ∘ (Tuple.sort f)) 3
            = ∑ i : Fin 4, f ((Tuple.sort f) i) := by
              norm_num [Fin.sum_univ_four]

          -- combine squared terms into sum
          have sum_sq_eq : ((f ∘ (Tuple.sort f)) 0) ^ 2 + ((f ∘ (Tuple.sort f)) 1) ^ 2 + ((f ∘ (Tuple.sort f)) 2) ^ 2 + ((f ∘ (Tuple.sort f)) 3) ^ 2
            = ∑ i : Fin 4, ((· ^ 2) ∘ f) ((Tuple.sort f) i) := by
              norm_num [Fin.sum_univ_four]

          -- we have that the sum is equal to the sum squared
          have sum_eq_sum_sq : ∑ i : Fin 4, f ((Tuple.sort f) i) = ∑ i : Fin 4, ((· ^ 2) ∘ f) ((Tuple.sort f) i) := by
              -- sorting re-arranges the sum
              rw [Equiv.sum_comp, Equiv.sum_comp]
              norm_num [Fin.sum_univ_four, f]

              -- the sum applies because a + b + c + d = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
              exact hh

          -- use the proof for monotone f
          have app := this
            ((f ∘ (Tuple.sort f)) 0)
            ((f ∘ (Tuple.sort f)) 1)
            ((f ∘ (Tuple.sort f)) 2)
            ((f ∘ (Tuple.sort f)) 3)
            (f_pos ((Tuple.sort f) 0))
            (f_pos ((Tuple.sort f) 1))
            (f_pos ((Tuple.sort f) 2))
            (f_pos ((Tuple.sort f) 3))

          -- use sum equalities
          rw [sum_eq, sum_sq_eq] at app
          replace app := app sum_eq_sum_sq

          -- a function which applies some function to each element is equal to the applied function itself
          have sorted_f_eq : ![(f ∘ (Tuple.sort f)) 0, (f ∘ (Tuple.sort f)) 1, (f ∘ (Tuple.sort f)) 2, (f ∘ (Tuple.sort f)) 3]
            = f ∘ (Tuple.sort f) := by ext i; fin_cases i <;> rfl

          -- simplify
          simp only [sorted_f_eq] at app

          -- f is monotone after sorting
          have mono : Monotone (f ∘ (Tuple.sort f)) := Tuple.monotone_sort f

          replace app := app mono

          -- combine terms into product
          have prod_sorted : (x - (f ∘ (Tuple.sort f)) 0) * (x - (f ∘ (Tuple.sort f)) 1)
            * (x - (f ∘ (Tuple.sort f)) 2) * (x - (f ∘ (Tuple.sort f)) 3)
            = ∏ i : Fin 4, ((x - f ·) ((Tuple.sort f) i)) := by
              norm_num [Fin.prod_univ_four]
          -- sorting re-arranges the product
          have prod_eq : ∏ i : Fin 4, ((x - f ·) ((Tuple.sort f) i)) = ∏ i : Fin 4, ((x - f ·) i) := by
              rw [Equiv.prod_comp (Tuple.sort f) (x - f ·)]

          -- simplify the product
          rw [prod_sorted, prod_eq] at app

          -- then we have our wanted bound
          convert app
          -- expand product
          · norm_num [Fin.prod_univ_four, f]

        -- so we have a ≤ b ≤ c ≤ d
        have a_le_b : a ≤ b := by
          have hm := hf (show (0 : Fin 4) ≤ 1 by omega)
          norm_num [f] at hm
          exact hm
        have b_le_c : b ≤ c := by
          have hm := hf (show (1 : Fin 4) ≤ 2 by omega)
          norm_num [f] at hm
          exact hm
        have c_le_d : c ≤ d := by
          have hm := hf (show (2 : Fin 4) ≤ 3 by omega)
          norm_num [f] at hm
          exact hm

      -- a balanced quadruple (a, b, c, d) implies that
      -- (a - (1 / 2)) ^ 2 + (b - (1 / 2)) ^ 2 + (c - (1 / 2)) ^ 2 + (d - (1 / 2)) ^ 2 = 1
        replace hh : (a - (1 / 2)) ^ 2 + (b - (1 / 2)) ^ 2 + (c - (1 / 2)) ^ 2 + (d - (1 / 2)) ^ 2 = 1 := by
          ring_nf
          linarith

        -- every term is positive, so the terms are at most 1
        -- we just need that d is at most 1 though
        have a_term : 0 ≤ (a - 1 / 2) ^ 2 := by positivity
        have b_term : 0 ≤ (b - 1 / 2) ^ 2 := by positivity
        have c_term : 0 ≤ (c - 1 / 2) ^ 2 := by positivity
        have d_term : (d - 1 / 2) ^ 2 ≤ 1 := by linarith

        -- so d is at most 3 / 2
        have d_le : d ≤ 3 / 2 := by
          -- assume that d is larger than 3 / 2
          by_contra lt_d
          norm_num at lt_d
          have inner : 1 < d - 1 / 2 := by linarith

          -- then the terms is larger than 1
          have squared : 1 < (d - 1 / 2) ^ 2 := by
            convert_to 1 * 1 < (d - 1 / 2) * (d - 1 / 2)
            · ring
            · ring
            gcongr

          -- contradiction
          linarith

        -- so every term of product is positive
        have d_term_pos : 0 ≤ (x - d) := by linarith
        have c_term_pos : 0 ≤ (x - c) := by linarith
        have b_term_pos : 0 ≤ (x - b) := by linarith
        have a_term_pos : 0 ≤ (x - a) := by linarith
        -- then total product is positive
        positivity