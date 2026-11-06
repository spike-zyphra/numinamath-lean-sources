import Mathlib

open Real Set

/- 3. Given $x, y \geq 1, x+y=8$, then the maximum value of $\left|\sqrt{x-\frac{1}{y}}+\sqrt{y-\frac{1}{x}}\right|$ is -/

-- lemma that x - y⁻¹ is positive for x, y ≥ 1, used multiple times in proof
lemma l_one_div_le_of_le_one_of_le_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 0 ≤ x - y⁻¹ := by
  suffices 1 / y ≤ x by simp at this; linarith
  apply div_le_of_le_mul₀
  . linarith
  . linarith
  . exact one_le_mul_of_one_le_of_one_le hx hy

-- lemma that x + 1/x is nondecreasing on (1, ∞), we factorize to products which are nonnegative
lemma l_add_one_div_mono_on_Ico_one : MonotoneOn (fun (x : ℝ) ↦ x + 1 / x) (Ici 1) := by
  rintro x hx y hy hxy
  simp at hx hy ⊢
  suffices 0 ≤ (y-x) + (y⁻¹-x⁻¹) by linarith
  convert_to 0 ≤ (y - x) * (x * y - 1) / (x * y)
  . field_simp
    ring
  have : 0 ≤ x * y - 1 := by
    apply sub_nonneg_of_le
    exact one_le_mul_of_one_le_of_one_le hx hy
  have : 0 ≤ y - x := by linarith
  positivity

-- the following function is nondecreasing on (1, ∞), this uses last lemma and is used in final step
lemma l_fun_mono_on_Ico_one : MonotoneOn (fun x ↦ 8 - 8 / x +  √ (x + 1 / x - 2) * 2) (Ici 1) := by
  rintro x hx y hy hxy
  simp at hx hy ⊢
  gcongr 8 - 8 / ?_ + ?_ * 2
  apply sqrt_le_sqrt
  apply sub_le_sub _ (by simp)
  convert l_add_one_div_mono_on_Ico_one hx hy hxy using 1 <;> simp

theorem algebra_136687 :
    IsGreatest {|√(x - 1 / y) + √(y - 1 / x)| | (x : ℝ) (y : ℝ) (_ : 1 ≤ x) (_ : 1 ≤ y)
    (_ : x + y = 8)} (√15) := by
  constructor
  -- to prove belongs to set, use 4, 4 as witness
  . simp
    use 4, 4
    norm_num
    rw [show (4 : ℝ) = 2^2 by norm_num]
    simp
  -- to prove upper bound, use first lemma to convert the expression to that of function of lemma
  . rintro z ⟨x, y, hx, hy, hxy, hz⟩
    rw [← hz, ← sq_le_sq₀ (by positivity) (by positivity)]
    simp
    ring_nf
    rw [sq_sqrt (l_one_div_le_of_le_one_of_le_one hx hy), sq_sqrt
        (l_one_div_le_of_le_one_of_le_one hy hx), ← sqrt_mul (l_one_div_le_of_le_one_of_le_one
        hx hy)]
    ring_nf
    -- now use x + y = 8 to convert to exactly function format
    convert_to 8 - 8 / (x * y) + √(x * y + 1 / (x * y) - 2) * 2 ≤ 15 using 2
    . rw [hxy]
      congr
      rw [← hxy]
      field_simp
      ring
    . congr 2
      rw [show x * x⁻¹ = 1 by field_simp, show y * y⁻¹ = 1 by field_simp]
      ring
    -- to apply monotonicity of the function we need 1 ≤ x * y
    have h_one_le_xy : 1 ≤ x * y := by
      exact one_le_mul_of_one_le_of_one_le hx hy
    -- x * y has upper bound 16 by am-gm of 2 variables
    have h_xy_le_sixteen : x * y ≤ 16 := by
      have : x * y ≤ (x + y)^2 / 4 := by
        linarith [show 0 ≤ (x - y)^2 by positivity]
      rw [hxy] at this
      norm_num at this
      assumption
    -- write the target as f(x*y) ≤ f(16), then use monotonicity
    let f := (fun x ↦ 8 - 8 / x +  √ (x + 1 / x - 2) * 2)
    convert_to f (x * y) ≤ f 16
    . simp [f]
      norm_num
      rw [show (225: ℝ) = 15^2 by norm_num, show (16: ℝ) = 4^2 by norm_num]
      simp
      norm_num
    apply l_fun_mono_on_Ico_one h_one_le_xy (by norm_num) h_xy_le_sixteen