import Mathlib

/- 4.3. $23 \star \star$ Let $a, b, c$ be positive real numbers, prove that:

$$

\frac{\sqrt{b+c}}{a}+\frac{\sqrt{c+a}}{b}+\frac{\sqrt{a+b}}{c} \geqslant \frac{4(a+b+c)}{\sqrt{(a+b)(b+c)(c+a)}} .

$$
 -/
theorem inequalities_119502 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    √(b + c) / a + √(c + a) / b + √(a + b) / c ≥
    4 * (a + b + c) / √((a + b) * (b + c) * (c + a)) := by

    -- wlog, a ≤ b ≤ c
    wlog habc : a ≤ b ∧ b ≤ c
    -- a b c can be permuted without changing anything
    -- consider order cases
    · by_cases hab : a ≤ b
      · simp only [hab, true_and, not_le] at habc
        by_cases hac : a ≤ c
        · convert this a c b ha hc hb ⟨hac, le_of_lt habc⟩             using 1 <;> ring_nf
        · convert this c a b hc ha hb ⟨le_of_lt <| not_le.mp hac, hab⟩ using 1 <;> ring_nf
      · simp only [not_le] at hab
        by_cases hbc : b ≤ c
        · by_cases hac : a ≤ c
          · convert this b a c hb ha hc ⟨le_of_lt hab, hac⟩              using 1 <;> ring_nf
          · convert this b c a hb hc ha ⟨hbc, le_of_lt <| not_le.mp hac⟩ using 1 <;> ring_nf
        · by_cases hac : a ≤ c
          -- case not possible
          · linarith only [hab, hbc, hac]
          · convert this c b a hc hb ha ⟨le_of_lt <| not_le.mp hbc, le_of_lt hab⟩ using 1 <;> ring_nf

    -- so we have a ≤ b and b ≤ c
    have ⟨hab, hbc⟩ := habc

    -- a b and c are all nonnegative
    have a_nonneg : 0 ≤ a := le_of_lt ha
    have b_nonneg : 0 ≤ b := le_of_lt hb
    have c_nonneg : 0 ≤ c := le_of_lt hc

    -- use ≤
    rw [ge_iff_le]

    -- √((a + b) * (b + c) * (c + a)) is positive
    have pos : 0 < √((a + b) * (b + c) * (c + a)) := by positivity

    -- multiply both sides by √((a + b) * (b + c) * (c + a)) and cancel
    apply (div_le_iff₀ pos).mpr

    -- distribute multiplication
    rw [add_mul, add_mul]

    -- rewrite terms to group similar parts
    convert_to 4 * (a + b + c) ≤
      (√(b + c) * √(b + c)) / a * √((a + b) * (c + a))
      + (√(c + a) * √(c + a))/ b * √((a + b) * (b + c))
      + (√(a + b) * √(a + b)) / c * √((b + c) * (c + a))
    · congr 1
      congr 1
      all_goals
      · repeat rw [Real.sqrt_mul (by positivity)]
        ring

    -- Simplify using √x * √x = x
    repeat rw [Real.mul_self_sqrt (by positivity)]

    -- By the Cauchy-Schwarz inequality, we have √(x + y)(x + z) = x + √yz, for all x y z
    have sq_mul : ∀ {x y z}, 0 ≤ x → 0 ≤ y → 0 ≤ z → x + √(y * z) ≤ √((x + y)*(x + z)) := by
      intro x y z xh yh zh
      -- x and y are nonnegative
      have pos1 : ∀ (i : Fin (Nat.succ 0).succ), 0 ≤ ![x, y] i := by
        intro i
        fin_cases i
        · exact xh
        · exact yh
      -- x and z are nonnegative
      have pos2 : ∀ (i : Fin (Nat.succ 0).succ), 0 ≤ ![x, z] i := by
        intro i
        fin_cases i
        · exact xh
        · exact zh

      -- we apply Cauchy-Schwarz inequality to (x, y) and (x, z)
      have cauchy := Real.sum_sqrt_mul_sqrt_le Finset.univ pos1 pos2

      -- simplify Cauchy-Schwarz inequality
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at cauchy
      rw [Real.mul_self_sqrt (by positivity), ←Real.sqrt_mul (by positivity),
        ←Real.sqrt_mul (by positivity)] at cauchy

      -- now it's equal to what we wanted to prove
      exact cauchy

    -- change terms to make them permutations of each other
    convert_to 4 * (a + b + c) ≤
      (b + c) / a * √((a + b) * (a + c)) + (c + a) / b * √((b + a) * (b + c)) + (a + b) / c * √((c + b) * (c + a))
    · ring_nf

    -- lower bound each term
    have termwise : (b + c) / a * (a + √(b * c)) + (c + a) / b * (b + √(a * c)) + (a + b) / c * (c + √(b * a))
      ≤ (b + c) / a * √((a + b) * (a + c)) + (c + a) / b * √((b + a) * (b + c)) + (a + b) / c * √((c + b) * (c + a))
      := by
        gcongr
        · exact sq_mul (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
        · exact sq_mul (le_of_lt hb) (le_of_lt ha) (le_of_lt hc)
        · exact sq_mul (le_of_lt hc) (le_of_lt hb) (le_of_lt ha)

    -- then we just need to prove that the goal lower bound is less than or equal to our found lower bound
    refine le_trans ?_ termwise
    convert_to 4 * (a + b + c) ≤ (b + c + (b + c) * (√(b * c) / a)) + (c + a + (c + a) * (√(c * a) / b)) + (a + b + (a + b) * (√(a * b) / c))
    · congr
      all_goals
      · rw [mul_add, div_mul_cancel₀]
        ring_nf
        · positivity

    -- subtract 2 * (a + b + c) from both sides
    refine (sub_le_sub_iff_right (2 * (a + b + c))).mp ?_

    -- simplify both sides
    convert_to 2 * (a + b + c) ≤
      (b + c) * (√(b * c) / a) + ((c + a) * (√(c * a) / b)) + ((a + b) * (√(a * b) / c))
    · ring
    · ring

    -- split up RHS terms into sequences: f and g
    let f := ![a + b, c + a, b + c]
    have f_0 : f 0 = a + b := rfl
    have f_1 : f 1 = c + a := rfl
    have f_2 : f 2 = b + c := rfl

    let g := ![√(a * b) / c, √(c * a) / b, √(b * c) / a]
    have g_0 : g 0 = √(a * b) / c := rfl
    have g_1 : g 1 = √(c * a) / b := rfl
    have g_2 : g 2 = √(b * c) / a := rfl

    convert_to 2 * (a + b + c) ≤ ∑ i : Fin 3, f i * g i
    · rw [Fin.sum_univ_three, f_0, f_1, f_2, g_0, g_1, g_2]
      ring

    -- we only need to check two inequalities to show that a triple is monotone
    have three_tuple_monotone : ∀ {f : Fin 3 → ℝ}, f 0 ≤ f 1 → f 1 ≤ f 2 → Monotone f := by
      intro f hf1 hf2
      have hf3 := le_trans hf1 hf2
      intro aa bb cc
      fin_cases aa
      · fin_cases bb
        · exact le_refl _
        · exact hf1
        · exact hf3
      · fin_cases bb
        · contradiction
        · exact le_refl _
        · exact hf2
      · fin_cases bb
        · contradiction
        · contradiction
        · exact le_refl _

    -- f is monotone
    have f_mono : Monotone f := by
      apply three_tuple_monotone
      · rw [f_0, f_1, add_comm]
        exact add_le_add_right hbc a
      · rw [f_1, f_2, add_comm]
        exact add_le_add_right hab c

    -- to prove that g is monotone, we prove a lemma that applies to both cases
    have sq_div_le : ∀ {x y z}, y ≤ z → 0 < x → 0 < y → 0 < z → √(x * y) / z ≤ √(z * x) / y := by
      intro x y z hyz hx hy hz
      refine div_le_div₀ (by positivity) ?_ hy hyz
      exact Real.sqrt_le_sqrt <| mul_comm x y ▸ mul_le_mul hyz (le_refl x) (le_of_lt hx) (le_of_lt hz)

    -- g is monotone
    have g_mono : Monotone g := by
      apply three_tuple_monotone
      · rw [g_0, g_1]
        exact sq_div_le hbc ha hb hc
      · rw [g_1, g_2]
        exact sq_div_le hab hc ha hb

    -- we use Chebyshev's Sum Inequality on f and g
    have cheby := (f_mono.monovary g_mono).sum_mul_sum_le_card_mul_sum

    -- simplify
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, Fintype.card_fin,
      Nat.cast_ofNat] at cheby

    -- 3 is positive
    have pos_three : (0 : ℝ) < 3 := by linarith only

    -- move 3 to LHS
    rw [←div_le_iff₀' pos_three, ←mul_div] at cheby

    -- chain inequalities
    refine le_trans ?_ cheby

    -- the sum of all f terms is equal to 2 * (a + b + c)
    have sum_eq : (∑ i : Fin 3, f i) = 2 * (a + b + c) := by
      rw [Fin.sum_univ_three, f_0, f_1, f_2]
      ring

    -- rewrite RHS
    rw [sum_eq]

    -- 2 * (a + b + c) is nonnegative
    have left_mul_pos : 0 ≤ 2 * (a + b + c) := by positivity

    -- both sides are multiplied by same value
    -- so to prove x ≤ x * y we prove 1 ≤ y
    refine le_mul_of_one_le_right left_mul_pos ?_

    -- every value of g is nonnegative
    have g_nonneg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
      intro i ih
      fin_cases i
      all_goals
      · simp only [g_0, g_1, g_2, Fin.reduceFinMk]
        positivity

    -- we use AM-GM with g (where each term has a weight of one)
    have am_gm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => 1) g (fun _ _ => by positivity) (by positivity) g_nonneg

    -- simplify AM-GM
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Real.rpow_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, one_mul] at am_gm

    -- the LHS of the AM-GM is equal to 1
    have prod_eq_one : (∏ x : Fin 3, g x) ^ (3 : ℝ)⁻¹ = 1 := by
      rw [Fin.prod_univ_three, g_0, g_1, g_2, div_mul_div_comm, div_mul_div_comm]
      field_simp
      ring_nf
      rw [Real.sq_sqrt a_nonneg, Real.sq_sqrt b_nonneg, Real.sq_sqrt c_nonneg]
      field_simp

    rw [prod_eq_one] at am_gm

    -- we're done
    exact am_gm