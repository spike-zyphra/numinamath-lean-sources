import Mathlib

set_option maxHeartbeats 400000

/-
$\underline{\text { Ivanov } K .}$

Real numbers $a, b, c, d$, each with absolute value greater than one, satisfy the relation $a b c + a b d + a c d + b c d + a + b + c + d = 0$

Prove that $\frac{1}{a-1}+\frac{1}{b-1}+\frac{1}{c-1}+\frac{1}{d-1}>0$
 -/
theorem algebra_221530 (a b c d : ℝ) (ha : |a| > 1) (hb : |b| > 1) (hc : |c| > 1) (hd : |d| > 1)
    (h : a * b * c + a * b * d + a * c * d + b * c * d + a + b + c + d = 0) :
    0 < 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) := by
  -- Обозначим $x=\frac{a+1}{a-1}, y=\frac{b+1}{b-1}, z=\frac{c+1}{c-1}, t=\frac{d+1}{d-1}$.
  let x := (a + 1) / (a - 1)
  let y := (b + 1) / (b - 1)
  let z := (c + 1) / (c - 1)
  let t := (d + 1) / (d - 1)
  -- Поскольку модули чисел $a, b, c, d$ больше единицы, числа $x, y, z, t$ положительны (и не равны 1 ).
  have x_pos_of_abs_a_gt_1 {a : ℝ} (ha : |a| > 1) : (a + 1) / (a - 1) > 0 := by
    by_cases w_a_nonneg : a ≥ 0
    . have : |a| = a := by
        exact abs_of_nonneg w_a_nonneg
      /-
      rw [this] at ha
      have : a - 1 > 0 := by
        --linarith
      have : a + 1 > 0 := by
        linarith
       -/
      field_simp
      linarith
    . simp at w_a_nonneg
      have : |a| = -a := by
        exact abs_of_neg w_a_nonneg
      rw [this] at ha
      have a_sub_1_neg : a - 1 < 0 := by
        linarith
      have a_add_1_neg : a + 1 < 0 := by
        linarith
      exact div_pos_of_neg_of_neg a_add_1_neg a_sub_1_neg
  have : x > 0 := x_pos_of_abs_a_gt_1 ha
  have : y > 0 := x_pos_of_abs_a_gt_1 hb
  have : z > 0 := x_pos_of_abs_a_gt_1 hc
  have : t > 0 := x_pos_of_abs_a_gt_1 hd
  -- Данное соотношение переписывается в виде $(a+1)(b+1)(c+1)(d+1)=(a-1)(b-1)(c-1)(d-1)$, или хуzt $=$ 1.
  have sub_1_eq_0_of_abs_gt_1 {a : ℝ} (ha : |a| > 1) : a - 1 ≠ 0 := by
    intro eq
    have : a = 1 := by
      linarith
    simp [this] at ha
  have := sub_1_eq_0_of_abs_gt_1 ha
  have := sub_1_eq_0_of_abs_gt_1 hb
  have := sub_1_eq_0_of_abs_gt_1 hc
  have := sub_1_eq_0_of_abs_gt_1 hd
  have prod_eq_1 : x * y * z * t = 1 := by
    unfold x y z t
    field_simp
    linarith
  -- Из равенства $\frac{1}{a-1}=\frac{x-1}{2}$ и аналогичных получаем, что $\frac{1}{a-1}+\frac{1}{b-1}+\frac{1}{c-1}+\frac{1}{d-1}=\frac{x+y+z+t-4}{2}$.
  have : 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) = (x + y + z + t - 4) / 2 := by
    unfold x y z t
    field_simp
    ring
  rw [this]
  -- Таким образом, надо доказать, что $x+y+z+t>4$.
  suffices x + y + z + t > 4 by
    linarith
  -- Поскольку $x y z t=1$, но числа $x, y, z, t$ отличны от единицы, среди них есть различные.
  have : ¬ (x = y ∧ x = z ∧ x = t) := by
    rintro ⟨x_eq_y, x_eq_z, x_eq_t⟩
    rw [← x_eq_y, ← x_eq_z, ← x_eq_t] at prod_eq_1
    rw [show x * x * x * x = x ^ 4 by ring] at prod_eq_1
    have : x ^ 4 = |x| ^ 4 := by
      have : x ^ 2 = |x| ^ 2 := by
        simp
      convert congrArg (. ^ 2) this using 1
      . ring
      . ring
    rw [this] at prod_eq_1
    have := Real.rpow_rpow_inv (x := |x|) (y := 4) (by simp) (by simp)
    rw [show |x| ^ (4 : ℝ) = |x| ^ 4 by norm_cast] at this
    simp [prod_eq_1] at this
    have abs_x_eq_1 : |x| = 1 := this.symm
    by_cases w_x_nonneg : x ≥ 0
    . --simp [w_x_nonneg] at abs_x_eq_1
      rw [abs_of_nonneg w_x_nonneg] at abs_x_eq_1
      unfold x at abs_x_eq_1
      field_simp at abs_x_eq_1
      linarith
    . simp at w_x_nonneg
      rw [abs_of_neg w_x_nonneg] at abs_x_eq_1
      unfold x at abs_x_eq_1
      field_simp at abs_x_eq_1
      linarith
  -- Поэтому по неравенству Коши $x+y+z+t>4 \sqrt[4]{x y z t}=4$
  have : x + y + z + t > 4 * (x * y * z * t) ^ (1 / 4 : ℝ) := by
    set geom_mean := x ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) * z ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ)
    set arith_mean := 1 / 4 * x + 1 / 4 * y + 1 / 4 * z + 1 / 4 * t
    have geom_mean_lt_arith_mean : geom_mean < arith_mean := by
      have geom_mean_le_arith_mean := Real.geom_mean_le_arith_mean4_weighted
        (w₁ := 1/4) (w₂ := 1/4) (w₃ := 1/4) (w₄ := 1/4)
        (p₁ := x) (p₂ := y) (p₃ := z) (p₄ := t)
        (by simp) (by simp) (by simp) (by simp)
        (by linarith) (by linarith) (by linarith) (by linarith)
        (by norm_num)
      have geom_mean_ne_arith_mean : geom_mean ≠ arith_mean := by
        intro eq
        let w : Fin 4 → ℝ := fun | 0 => x | 1 => y | 2 => z | 3 => t
        have : x = y ∧ x = z ∧ x = t := by
          have eq_iff := Real.geom_mean_eq_arith_mean_weighted_iff
            (ι := Fin 4)
            (s := Finset.univ)
            (fun _ => 1/4)
            w
            (by simp)
            (by simp)
            (by
              intro i hi
              fin_cases i <;>
              . simp [w]
                linarith
            )
          dsimp at eq_iff
          have : ∏ i : Fin 4, w i ^ (1 / 4 : ℝ) = ∑ i : Fin 4, 1 / 4 * w i := by
            rw [Fin.prod_univ_four, Fin.sum_univ_four]
            dsimp [w]
            exact eq
          have all_eq_arith_mean := eq_iff.mp this
          have := all_eq_arith_mean 0 (by simp) (by simp)
          conv_lhs at this => simp [w]
          have := all_eq_arith_mean 1 (by simp) (by simp)
          conv_lhs at this => simp [w]
          have := all_eq_arith_mean 2 (by simp) (by simp)
          conv_lhs at this => simp [w]
          have := all_eq_arith_mean 3 (by simp) (by simp)
          conv_lhs at this => simp [w]
          constructor
          . linarith
          constructor
          . linarith
          . linarith
        contradiction
      exact lt_of_le_of_ne geom_mean_le_arith_mean geom_mean_ne_arith_mean
    unfold geom_mean arith_mean at geom_mean_lt_arith_mean

    --generalize eq_x : x = x, eq_y : y = y, eq_z : z = z, eq_t : t = t
    --rw [eq_x, eq_y, eq_z, eq_t] at geom_mean_lt_arith_mean
    --ring_nf at geom_mean_le_arith_mean
    --linarith
    have : x ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) * z ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) =
        (x * y * z * t) ^ (1 / 4 : ℝ) := by
      --ring
      --nlinarith
      repeat rw [Real.mul_rpow (by nlinarith) (by linarith)]
    rw [this] at geom_mean_lt_arith_mean
    /- added when the `1 / 4` in the goal was mistakenly of type `ℕ`
    have : 1 / 4 * x + 1 / 4 * y + 1 / 4 * z + 1 / 4 * t = 1 / 4 * (x + y + z + t) := by
      ring
    rw [this] at geom_mean_le_arith_mean
    generalize h : x * y * z * t = prod
    rw [h] at geom_mean_le_arith_mean
    generalize h : x + y + z + t = sum
    rw [h] at geom_mean_le_arith_mean
    generalize h : prod ^ (1 / 4 : ℝ) = prod_fourth_root
    rw [h] at geom_mean_le_arith_mean
    -/
    linarith
  --linarith
  simp [prod_eq_1] at this
  exact this
