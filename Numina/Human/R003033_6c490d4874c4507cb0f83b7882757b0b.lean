import Mathlib

/- Given a sequence x of at least 2 elements where each is non-negative, and at least
  two elements are positive, then ∑ i, x_i - x_j is positive, for every j. -/
lemma Real_sum_sub_pos {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (i j : Fin n)
  (hij : i ≠ j) (hi : 0 < x i) (hj : 0 < x j) (jj : Fin n)
  : 0 < ∑ j : Fin n, x j - x jj := by
    -- n is at least 2, so replace n with n + 2
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := Nat.exists_eq_add_of_le' hn
    -- separate f jj from the sum
    rw [Fin.sum_univ_succAbove _ jj]

    -- simplify
    ring_nf
    -- then we just need to show that the remaining sum is positive
    refine Finset.sum_pos' ?_ ?_
    -- every term is non-negative
    · exact fun iii a => hx (jj.succAbove iii)
    -- and one term is positive
    · norm_num
      -- consider if jj = i, i.e. we removed i:th term from the sum
      by_cases jj_eq : jj = i
      -- then we still have the j:th term in the sum, which is positive
      · have jj_ne : jj ≠ j := ne_of_eq_of_ne jj_eq hij
        obtain ⟨j', jh'⟩ : ∃ j', (jj.succAbove j') = j
          := Fin.exists_succAbove_eq jj_ne.symm
        exists j'
        norm_num [jh', hj]
      -- consider if jj ≠ i
      -- then we still have the i:th term in the sum, which is positive
      · obtain ⟨i', ih'⟩ : ∃ i', (jj.succAbove i') = i
          := Fin.exists_succAbove_eq fun a => jj_eq a.symm
        exists i'
        norm_num [ih', hi]

/- Given a monotone sequence x of at least 2 elements where each is non-negative, and at least
  two elements are positive, then (∑ i, x_i - x_j)⁻¹ is a monotone sequence. -/
lemma Real_sum_sub_monotone {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (xm : Monotone x) (hx : ∀ i, 0 ≤ x i) (i j : Fin n)
  (hij : i ≠ j) (hi : 0 < x i) (hj : 0 < x j)
  : Monotone (fun i => 1 / (∑ j : Fin n, x j - x i)) := by
      intro ii jj hh
      refine one_div_le_one_div_of_le ?_ ?_
      · exact Real_sum_sub_pos hn x hx i j hij hi hj jj
      · gcongr
        exact xm hh

/- Given a sequence x of at least 2 elements where each is non-negative, and at least
  two elements are positive, then we have the sum bound:
  (1 / n) * (∑ (x_i ^ 3)) * (∑ (1 / ((∑ x_j) - x_i))) ≤ ∑ (x_i ^ 3 / ((∑ j, x_j) - x_i)) -/
lemma Real_sum_div_diff_le {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (i j : Fin n)
  (hij : i ≠ j) (hi : 0 < x i) (hj : 0 < x j)
  : (1 / n) * (∑ i, x i ^ 3) * (∑ i, (1 / ((∑ j, x j) - x i))) ≤ ∑ i, (x i ^ 3 / ((∑ j, x j) - x i)) := by
    -- wlog, x is monotone
    wlog hm : Monotone x
    -- else we sort x
    · have app := this (by tauto) (x ∘ (Tuple.sort x)) (hx <| Tuple.sort x <| ·)
        ((Tuple.sort x).symm i) ((Tuple.sort x).symm j)
        (by norm_num [hij])
        (by norm_num [hi])
        (by norm_num [hj])
        (Tuple.monotone_sort x)

      -- all our sums are invariant under equivalences, i.e. sorting x doesn't change the results
      simp only [Function.comp_apply] at app
      rw [Equiv.sum_comp (Tuple.sort x) (fun i => x i ^ 3),
        Equiv.sum_comp (Tuple.sort x) x,
        Equiv.sum_comp (Tuple.sort x) (fun i => 1 / (∑ i : Fin n, x i - x i)),
        Equiv.sum_comp (Tuple.sort x) (fun i => (x i) ^ 3 / (∑ i : Fin n, x i - x i))] at app
      tauto

    -- consider the sequence f(i) = ((∑ x) - x i)⁻¹
    let f := fun i => 1 / (∑ j : Fin n, x j - x i)
    -- and g(i) = x i ^ 3
    let g := (· ^ 3) ∘ x

    -- then f is monotone
    have f_mono : Monotone f := Real_sum_sub_monotone hn x hm hx i j hij hi hj

    -- then x is monotone
    have g_mono : Monotone g := by
      -- because it's a composition of monotone functions
      refine Monotone.comp ?_ hm
      -- three is odd
      have three_odd : Odd 3 := by decide
      -- so (· ^ 3) is monotone
      exact three_odd.strictMono_pow.monotone

    -- so we can use Chebyshev's Sum Inequality with the sequences f and g
    have cheby := (g_mono.monovary f_mono).sum_mul_sum_le_card_mul_sum

    -- simplify
    norm_num at cheby

    -- note that n is positive
    have n_ne : 0 < (n : ℝ) := by norm_cast; omega

    -- so we can reorder Chebyshev in the form we wanted to prove
    replace cheby : (1 / n) * (∑ i : Fin n, g i) * ∑ i : Fin n, f i ≤ ∑ i : Fin n, g i * f i := by
      field_simp
      exact (div_le_iff₀' n_ne).mpr cheby

    -- we're pretty much done
    convert cheby using 1
    -- simplify
    norm_num [f, g]
    -- everything is (essentially) equal
    congr


/- Given a sequence x of at least 2 elements where each is non-negative, and at least
  two elements are positive, then we have the sum bound:
  n ^ 2 / ((n - 1) * ∑ x i) ≤ ∑ ((∑ j, x j) - x i)⁻¹ -/
lemma Real_sum_div_diff_le' {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (i j : Fin n)
  (hij : i ≠ j) (hi : 0 < x i) (hj : 0 < x j)
  : n ^ 2 / ((n - 1) * ∑ i, x i) ≤ ∑ i, (1 / ((∑ j, x j) - x i)) := by
    -- wlog, x is monotone
    wlog hm : Monotone x
    -- else we sort x
    · have app := this (by tauto) (x ∘ (Tuple.sort x)) (hx <| Tuple.sort x <| ·)
        ((Tuple.sort x).symm i) ((Tuple.sort x).symm j)
        (by norm_num [hij])
        (by norm_num [hi])
        (by norm_num [hj])
        (Tuple.monotone_sort x)

      -- all our sums are invariant under equivalences, i.e. sorting x doesn't change the results
      simp only [Function.comp_apply] at app
      rw [Equiv.sum_comp (Tuple.sort x) x,
        Equiv.sum_comp (Tuple.sort x) (fun i => 1 / (∑ i : Fin n, x i - x i))] at app
      tauto

    -- consider the sequence f(i) = ((∑ x) - x i)⁻¹
    let f := fun k => 1 / (∑ j : Fin n, x j - x k)

    -- and g(i) = (∑ x) - x i
    let g := fun k => ∑ j : Fin n, x j - x k

    -- then f is monotone
    have f_mono : Monotone f := Real_sum_sub_monotone hn x hm hx i j hij hi hj
    -- and g is antitone
    have g_mono : Antitone g := by
      intro i j ij
      exact tsub_le_tsub_left (by tauto) _

    -- so we can use Chebyshev's Sum Inequality with the sequences f and g
    have cheby := (g_mono.antivary f_mono).card_mul_sum_le_sum_mul_sum

    -- g * f is 1
    have mul_eq : ∀ i, g i * f i = 1 := by
      intro k
      refine mul_one_div_cancel ?_
      suffices : 0 < ∑ j : Fin n, x j - x k
      · positivity
      exact Real_sum_sub_pos hn x hx i j hij hi hj k

    -- simplify
    norm_num [mul_eq, g] at cheby

    -- simplify Chebyshev to make it into the form we wanted
    convert_to ↑n ^ 2 ≤ ((↑n - 1) * ∑ j : Fin n, x j) * ∑ i : Fin n, f i at cheby
    · ring
    · ring

    -- cancel division
    rw [div_le_iff₀]

    -- then Chebyshev's fit
    linarith
    -- we use that (n - 1) * (∑ x) is positive
    -- left factor is positive
    · have left_pos : 0 < ((n : ℝ) - 1) := by
        norm_num
        omega
      -- right factor is positive
      have right_pos : 0 < ∑ i : Fin n, x i := by
        -- extract term i
        obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := Nat.exists_eq_add_of_le' hn
        rw [Fin.sum_univ_succAbove _ i]
        -- the remaining sum is non-negative
        have sum_nonneg : 0 ≤ ∑ i_1 : Fin (n + 1), x (i.succAbove i_1) := by
          apply Finset.sum_nonneg
          · norm_num
            intro k
            exact hx (i.succAbove k)
        -- so total sum is positive
        positivity
      -- so product is positive
      positivity

/- x + (1 / x) is at least 2, when x is positive. -/
lemma Real_two_le_add_inv_of_pos (x : ℝ) (h : 0 < x) : 2 ≤ x + (1 / x) := by

  -- multiply both sides by x
  suffices : 2 * x ≤ (x + 1 / x) * x
  · nlinarith

  -- multiplication distributes
  have mul_distrib : (x + 1 / x) * x = x ^ 2 + 1 := by
    field_simp
    ring
  rw [mul_distrib]

  -- move terms to RHS
  suffices : 0 ≤ x ^ 2 - 2 * x + 1
  · nlinarith

  -- offset the graph to the right
  obtain ⟨x', xh⟩ : ∃ x', x = x' + 1 := by
    exists x - 1
    linarith

  subst xh
  ring_nf

  -- clearly x' ^ 2 is positive
  positivity

/- Let $a, b, c, d \geq 0$ such that $a b+b c+c d+d a=1$. Show that:


$$

\frac{a^{3}}{b+c+d}+\frac{b^{3}}{a+c+d}+\frac{c^{3}}{a+b+d}+\frac{d^{3}}{a+b+c} \geq \frac{1}{3}

$$
 -/
theorem inequalities_146933 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a * b + b * c + c * d + d * a = 1) :
    1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (a + c + d) + c ^ 3 / (a + b + d) +
    d ^ 3 / (a + b + c)
  := by
    -- list the variables as f(0) = a, f(1) = b, f(2) = c, f(3) = d
    let f : Fin 4 → ℝ := ![a, b, c, d]

    -- all variables are non-negative
    have f_nonneg : ∀ i, 0 ≤ f i := by
      intro i
      fin_cases i <;> (norm_num [f]; tauto)

    -- we have that (a + c) * (b + d) = 1
    have hh : (a + c) * (b + d) = 1 := by linarith

    -- so then b + d is equal to 1 / (a + c)
    have add_eq : b + d = 1 / (a + c)
      := eq_one_div_of_mul_eq_one_right hh

    --
    have sum_bound : 2 ≤ ∑ i : Fin 4, f i := by
      -- group terms
      convert_to 2 ≤ (a + c) + (b + d)
      · norm_num [Fin.sum_univ_four, f]
        ring

      rw [add_eq]

      -- positive real number added to it's inverse is at least 2
      apply Real_two_le_add_inv_of_pos
      -- we have that the number is non-negative
      · have nonneg : 0 ≤ a + c := by positivity

        -- consider when it's equal to zero
        by_cases eq_zero : a + c = 0
        -- that's impossible
        · norm_num [eq_zero] at hh
        -- so it's positive
        · positivity

    -- So we want to prove a lower bound of a sum over f values
    convert_to 1 / 3 ≤ ∑ i, (f i ^ 3 / ((∑ j, f j) - f i))
    · rw [Fin.sum_univ_four, Fin.sum_univ_four]
      norm_num [f]
      ring

    -- at least two f values are positive, because of a * b + b * c + c * d + d * a = 1
    obtain ⟨i, j, ij, hi, hj⟩ : ∃ i j, i ≠ j ∧ 0 < f i ∧ 0 < f j := by

      -- each term is non-negative
      have ab_nonneg : 0 ≤ a * b := by positivity
      have bc_nonneg : 0 ≤ b * c := by positivity
      have cd_nonneg : 0 ≤ c * d := by positivity
      have da_nonneg : 0 ≤ d * a := by positivity

      -- so at least one term is positive
      have either_pos : 0 < a * b ∨ 0 < b * c ∨ 0 < c * d ∨ 0 < d * a := by
        by_contra hh
        norm_num at hh
        linarith

      -- consider each case
      rcases either_pos with ab | bc | cd | da
      -- a * b is positive, so a and b are positive
      · have a_pos : 0 < a := pos_of_mul_pos_left ab hb
        have b_pos : 0 < b := pos_of_mul_pos_right ab ha
        exists 0, 1
      -- b * c is positive, so b and c are positive
      · have b_pos : 0 < b := pos_of_mul_pos_left bc hc
        have c_pos : 0 < c := pos_of_mul_pos_right bc hb
        exists 1, 2
      -- c * d is positive, so c and d are positive
      · have c_pos : 0 < c := pos_of_mul_pos_left cd hd
        have d_pos : 0 < d := pos_of_mul_pos_right cd hc
        exists 2, 3
      -- d * a is positive, so d and a are positive
      · have d_pos : 0 < d := pos_of_mul_pos_left da ha
        have a_pos : 0 < a := pos_of_mul_pos_right da hd
        exists 3, 0

    -- we have a lower bound of (1 / 4) * (∑ f i ^ 3) * (∑ ((∑ f j) - f i))⁻¹)
    have bound_1 : (1 / 4) * (∑ i, f i ^ 3) * (∑ i, (1 / ((∑ j, f j) - f i))) ≤ ∑ i, (f i ^ 3 / ((∑ j, f j) - f i))
      := Real_sum_div_diff_le (by tauto) f f_nonneg i j ij hi hj

    refine le_trans ?_ bound_1

    -- using mean value inequality we have
    -- (1 / 16) * (∑ f) ^ 3 ≤ ∑ f i ^ 3
    have means_ineq : (1 / 16) * (∑ i : Fin 4, f i) ^ 3 ≤ ∑ i : Fin 4, f i ^ 3 := by
      have mvi := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => 1 / 4) f (by norm_num) (by norm_num)
        (fun i a => f_nonneg i) 3
      -- simplify
      rw [←Finset.mul_sum, ←Finset.mul_sum] at mvi

      -- then we have our inequality
      linarith

    -- which has a bound without power of three, as
    -- (1 / 4) * (∑ f) ≤ (1 / 16) * (∑ f) ^ 3
    have without_pow_three : (1 / 4) * (∑ i : Fin 4, f i) ≤ (1 / 16) * (∑ i : Fin 4, f i) ^ 3 := by
      have sum_pos : 0 < ∑ i : Fin 4, f i := by linarith
      suffices : 1 * (∑ i : Fin 4, f i) ≤ (1 / 4 * (∑ i : Fin 4, f i) ^ 2) * (∑ i : Fin 4, f i)
      · linarith
      gcongr

      suffices : 2 ^ 2 ≤ (∑ i : Fin 4, f i) ^ 2
      · linarith

      exact (sq_le_sq₀ (by positivity) (by positivity)).mpr sum_bound

    -- we can bound the three factors of RHS separately
    trans (1 / 4) * (1 / 4 * ∑ i : Fin 4, f i) * (16 / (3 * ∑ i : Fin 4, f i))
    · ring_nf
      field_simp

    gcongr
    -- 1 / 4 * ∑ f i ^ 3 is non-negative
    · suffices : 0 ≤ ∑ i : Fin 4, f i ^ 3
      · linarith
      apply Finset.sum_nonneg
      · norm_num
        intro i
        exact pow_nonneg (f_nonneg i) 3
    -- we have that 1 / 4 * ∑ f ≤ ∑ f i ^ 3 using mean inequalities
    · trans (1 / 16) * (∑ i : Fin 4, f i) ^ 3
      · exact without_pow_three
      · exact means_ineq
    -- we have that 16 / (3 * ∑ f) ≤ ∑ ((∑ f) - f i)⁻¹
    · have bound_2 := @Real_sum_div_diff_le' 4 (by omega) f f_nonneg i j ij hi hj
      -- normalize
      norm_num at bound_2 ⊢
      -- then they're equal
      exact bound_2