import Mathlib

open Real

/-
Let $a, b, c$ be the sides of a triangle. Prove that  $$ \frac{\sqrt{b+c-a}}{\sqrt{b}+\sqrt{c}-\sqrt{a}}+\frac{\sqrt{c+a-b}}{\sqrt{c}+\sqrt{a}-\sqrt{b}}+\frac{\sqrt{a+b-c}}{\sqrt{a}+\sqrt{b}-\sqrt{c}} \leq 3 . $$
-/

set_option maxHeartbeats 200000 in
theorem Algebra_a5
    (a b c : ℝ)
    (h_pos : 0 < a ∧ 0 < b ∧ 0 < c)
    (hc1 : a + b > c)
    (hb1 : c + a > b)
    (ha1 : b + c > a) :
    √(b + c - a) / (√b + √c - √a) +
    √(c + a - b) / (√c + √a - √b) +
    √(a + b - c) / (√a + √b - √c) ≤ 3 := by
  have ha_pos : 0 < a := h_pos.1
  have hb_pos : 0 < b := h_pos.2.1
  have hc_pos : 0 < c := h_pos.2.2
  have h_sqrt_convex : ∀ x > 0, ∀ y > 0, √(x + y) ≤ √x + √y := by
    intro x hx y hy
    let x' : NNReal := ⟨x, by positivity⟩
    let y' : NNReal := ⟨y, by positivity⟩
    simp only [Real.sqrt_eq_rpow]
    suffices h : (x' + y') ^ (1 / 2 : ℝ) ≤ x' ^ (1 / 2 : ℝ) + y' ^ (1 / 2 : ℝ) by
      rw [← NNReal.coe_le_coe] at h
      simpa [x', y'] using h
    apply NNReal.rpow_add_le_add_rpow <;> norm_num
  -- Note first that the denominators are all positive, e.g. $\sqrt{a}+\sqrt{b}>\sqrt{a+b}>\sqrt{c}$.
  have ha2 : 0 < √b + √c - √a := by
    suffices √a < √b + √c by
      linarith
    have : √(b + c) > √a := by simp only [gt_iff_lt]; rwa [Real.sqrt_lt_sqrt_iff_of_pos]; positivity
    apply lt_of_lt_of_le this
    apply h_sqrt_convex _ (by positivity) _ (by positivity)
  have hb2 : 0 < √c + √a - √b := by
    suffices √b < √c + √a by
      linarith
    have : √(c + a) > √b := by simp only [gt_iff_lt]; rwa [Real.sqrt_lt_sqrt_iff_of_pos]; positivity
    apply lt_of_lt_of_le this
    apply h_sqrt_convex _ (by positivity) _ (by positivity)
  have hc2 : 0 < √a + √b - √c := by
    suffices √c < √a + √b by
      linarith
    have : √(a + b) > √c := by simp only [gt_iff_lt]; rwa [Real.sqrt_lt_sqrt_iff_of_pos]; positivity
    apply lt_of_lt_of_le this
    apply h_sqrt_convex _ (by positivity) _ (by positivity)
  -- Let $x=\sqrt{b}+\sqrt{c}-\sqrt{a}, y=\sqrt{c}+\sqrt{a}-\sqrt{b}$ and $z=\sqrt{a}+\sqrt{b}-\sqrt{c}$.
  let x := √b + √c - √a
  let y := √c + √a - √b
  let z := √a + √b - √c
  -- Then  $b+c-a=\left(\frac{z+x}{2}\right)^{2}+\left(\frac{x+y}{2}\right)^{2}-\left(\frac{y+z}{2}\right)^{2}=\frac{x^{2}+x y+x z-y z}{2}=x^{2}-\frac{1}{2}(x-y)(x-z)$
  have ha3 : b + c - a = x^2 - (x - y) * (x - z) / 2 := by
    calc
     _ = ((z + x) / 2)^2 + ((x + y) / 2)^2 - ((y + z) / 2)^2 := by
      simp [x, y, z]
      ring_nf
      rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
      · ring
      all_goals positivity
    _ = ((z + x) / 2)^2 + ((x + y) / 2)^2 - ((y + z) / 2)^2 := by simp [x, y, z]
    _ = (x^2 + x*y + x*z - y*z) / 2 := by ring
    _ = _ := by ring
  -- and  $$ \frac{\sqrt{b+c-a}}{\sqrt{b}+\sqrt{c}-\sqrt{a}}=\sqrt{1-\frac{(x-y)(x-z)}{2 x^{2}}} \leq 1-\frac{(x-y)(x-z)}{4 x^{2}} $$  applying $\sqrt{1+2 u} \leq 1+u$ in the last step.
  have ha4 : √(b + c - a) / (√b + √c - √a) ≤ 1 - (x - y) * (x - z) / (4 * x^2) := by
    calc
      _ = √(b + c - a) / x := rfl
      _ = √(1 - (x - y) * (x - z) / (2 * x^2)) := by
        rw [ha3]
        conv => lhs; arg 2; rw [← @Real.sqrt_sq x (by simp [x]; linarith)]
        rw [← Real.sqrt_div' _ (sq_nonneg x)]
        congr
        rw [sub_div]
        congr 1
        · rw [div_self]
          simp [x]
          positivity
        · rw [div_div]
      _ ≤ _ := by
        rw [sub_eq_add_neg]
        convert Real.sqrt_one_add_le _ using 1
        · rw [neg_div', div_div]
          ring_nf
        · simp
          rw [div_le_one₀ (by simp [x]; positivity)]
          simp [x, y, z]
          ring_nf
          rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
          · linarith
          all_goals positivity
  -- Similarly we obtain  $$ \frac{\sqrt{c+a-b}}{\sqrt{c}+\sqrt{a}-\sqrt{b}} \leq 1-\frac{(z-x)(z-y)}{4 z^{2}}$$
  have hb3 : c + a - b = y^2 - (y - z) * (y - x) / 2 := by
    calc
     _ = ((x + y) / 2)^2 + ((y + z) / 2)^2 - ((z + x) / 2)^2 := by
      simp [x, y, z]
      ring_nf
      rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
      · ring
      all_goals positivity
    _ = ((x + y) / 2)^2 + ((y + z) / 2)^2 - ((z + x) / 2)^2 := by simp [x, y, z]
    _ = (y^2 + y*z + y*x - z*x) / 2 := by ring
    _ = _ := by ring
  have hb4 : √(c + a - b) / (√c + √a - √b) ≤ 1 - (y - z) * (y - x) / (4 * y^2) := by
    calc
      _ = √(c + a - b) / y := rfl
      _ = √(1 - (y - z) * (y - x) / (2 * y^2)) := by
        rw [hb3]
        conv => lhs; arg 2; rw [← @Real.sqrt_sq y (by simp [y]; linarith)]
        rw [← Real.sqrt_div' _ (sq_nonneg y)]
        congr
        rw [sub_div]
        congr 1
        · rw [div_self]
          simp [y]
          positivity
        · rw [div_div]
      _ ≤ _ := by
        rw [sub_eq_add_neg]
        convert Real.sqrt_one_add_le _ using 1
        · rw [neg_div', div_div]
          ring_nf
        · simp
          rw [div_le_one₀ (by simp [y]; positivity)]
          simp [x, y, z]
          ring_nf
          rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
          · linarith
          all_goals positivity
  -- and $$ \frac{\sqrt{a+b-c}}{\sqrt{a}+\sqrt{b}-\sqrt{c}} \leq 1-\frac{(y-z)(y-x)}{4 y^{2}} $$.
  have hc3 : a + b - c = z^2 - (z - x) * (z - y) / 2 := by
    calc
     _ = ((y + z) / 2)^2 + ((z + x) / 2)^2 - ((x + y) / 2)^2 := by
      simp [x, y, z]
      ring_nf
      rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
      · ring
      all_goals positivity
    _ = ((y + z) / 2)^2 + ((z + x) / 2)^2 - ((x + y) / 2)^2 := by simp [x, y, z]
    _ = (z^2 + z*x + z*y - x*y) / 2 := by ring
    _ = _ := by ring
  have hc4 : √(a + b - c) / (√a + √b - √c) ≤ 1 - (z - x) * (z - y) / (4 * z^2) := by
    calc
      _ = √(a + b - c) / z := rfl
      _ = √(1 - (z - x) * (z - y) / (2 * z^2)) := by
        rw [hc3]
        conv => lhs; arg 2; rw [← @Real.sqrt_sq z (by simp [z]; linarith)]
        rw [← Real.sqrt_div' _ (sq_nonneg z)]
        congr
        rw [sub_div]
        congr 1
        · rw [div_self]
          simp [z]
          positivity
        · rw [div_div]
      _ ≤ _ := by
        rw [sub_eq_add_neg]
        convert Real.sqrt_one_add_le _ using 1
        · rw [neg_div', div_div]
          ring_nf
        · simp
          rw [div_le_one₀ (by simp [z]; positivity)]
          simp [x, y, z]
          ring_nf
          rw [Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
          · linarith
          all_goals positivity
  -- Substituting these quantities into the statement, it is sufficient to prove that  $$ \frac{(x-y)(x-z)}{x^{2}}+\frac{(y-z)(y-x)}{y^{2}}+\frac{(z-x)(z-y)}{z^{2}} \geq 0 . $$
  suffices h : (x - y) * (x - z) / x^2 + (y - x) * (y - z) / y^2 + (z - x) * (z - y) / z^2 ≥ 0 by
    replace h : (x - y) * (x - z) / (4 * x^2) + (y - x) * (y - z) / (4 * y^2) + (z - x) * (z - y) / (4 * z^2) ≥ 0 := by
      have := div_nonneg h (show 0 ≤ 4 by norm_num)
      simp [add_div] at this
      rw [div_div, div_div, div_div] at this
      convert this.ge using 3
      · congr 1; ring
      · congr 1; ring
      · ring
    have := add_le_add (add_le_add (add_le_add ha4 hb4) hc4) h
    simp at this
    convert this
    ring
  -- By symmetry we can assume $x \leq y \leq z$.
  suffices h : ∀ (x y z : ℝ), (0 < x) → (0 < y) → (0 < z) → (x ≤ y) → (y ≤ z) → (x - y) * (x - z) / x^2 + (y - x) * (y - z) / y^2 + (z - x) * (z - y) / z^2 ≥ 0 by
    have hx_pos : 0 < x := ha2
    have hy_pos : 0 < y := hb2
    have hz_pos : 0 < z := hc2
    by_cases hxy : x ≤ y <;> by_cases hyz : y ≤ z <;> by_cases hzx : z ≤ x <;> {
      simp only [not_le] at hxy hyz hzx
      first
      | linarith only [hxy, hyz, hzx]
      | convert h x y z hx_pos hy_pos hz_pos (by linarith only [hxy, hyz, hzx]) (by linarith only [hxy, hyz, hzx]) using 1
      | convert h x z y hx_pos hz_pos hy_pos (by linarith only [hxy, hyz, hzx]) (by linarith only [hxy, hyz, hzx]) using 1 <;> ring
      | convert h y x z hy_pos hx_pos hz_pos (by linarith only [hxy, hyz, hzx]) (by linarith only [hxy, hyz, hzx]) using 1 <;> ring
      | convert h y z x hy_pos hz_pos hx_pos (by linarith only [hxy, hyz, hzx]) (by linarith only [hxy, hyz, hzx]) using 1 <;> ring
      | convert h z x y hz_pos hx_pos hy_pos (by linarith only [hxy, hyz, hzx]) (by linarith only [hxy, hyz, hzx]) using 1 <;> ring
      | convert h z y x hz_pos hy_pos hx_pos (by linarith only [hxy, hyz, hzx]) (by linarith only [hxy, hyz, hzx]) using 1; ring
    }
  -- Then  $$ \begin{gathered} \frac{(x-y)(x-z)}{x^{2}}=\frac{(y-x)(z-x)}{x^{2}} \geq \frac{(y-x)(z-y)}{y^{2}}=-\frac{(y-z)(y-x)}{y^{2}}
  intro x y z hx hy hz hxy hyz
  have hxy' : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hyz' : 0 ≤ z - y := sub_nonneg.mpr hyz
  have hxz' : 0 ≤ z - x := sub_nonneg.mpr (hxy.trans hyz)
  have h6 : (x - y) * (x - z) / x^2 ≥ - ((y - x) * (y - z) / y^2) := by
    calc
      _ = (y - x) * (z - x) / x^2 := by ring
      _ ≥ (y - x) * (z - x) / y^2 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · gcongr
      _ ≥ (y - x) * (z - y) / y^2 := by
        apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · linarith
          · positivity
        · positivity
      _ = _ := by ring
  -- \\ \frac{(z-x)(z-y)}{z^{2}} \geq 0 \end{gathered} $$
  have h7 : (z - x) * (z - y) / z^2 ≥ 0 :=
    div_nonneg (mul_nonneg hxz' hyz') (sq_nonneg z)
  -- and (1) follows.
  rw [ge_iff_le, neg_le_iff_add_nonneg] at h6
  positivity
