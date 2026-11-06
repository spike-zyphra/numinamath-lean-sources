import Mathlib

open Real Set
open scoped BigOperators

/- Find all non-zero real numbers $x$ such that
\[\min \left\{ 4, x+ \frac 4x \right\} \geq 8 \min \left\{ x,\frac 1x\right\} .\] -/
theorem inequalities_77111 {x : ℝ} (hx : x ≠ 0) :
    min 4 (x + 4 / x) ≥ 8 * min x (1 / x) ↔
    x ∈ Iio 0 ∪ Ioc 0 (1 / 2) ∪ Ici 2 := by
  -- Remark $\boxed{\boxed{\min\{a,\ b\}=\frac{a+b}{2}-\frac{|a-b|}{2}}}$ ,
  have hmin_eq {a b : ℝ} : min a b = (a + b) / 2 - |a - b| / 2 := by
    by_cases h : a < b
    · have : |a - b| = b - a := by
        trans - (a - b)
        · refine abs_of_neg ?_
          simp [h]
        · ring
      simp [le_of_lt h, this]
      ring
    · simp at h
      have : |a - b| = a - b := by
        apply abs_of_nonneg
        exact sub_nonneg_of_le h
      simp [h, this]
      ring
  -- $\min\left\{4,\ x+\frac{4}{x}\right\}\geq 8\min\left\{x,\
  -- \frac{1}{x}\right\}\ (x\neq 0)$
  -- $\Longleftrightarrow \frac{x+\frac{4}{x}+4}{2}-\frac{\left|x+\frac{4}{x}-4\right|}{2}\geq 8\left(\frac{x+\frac{1}{x}}{2}-\frac{\left|x-\frac{1}{x}\right|}{2}\right)$
  -- $\Longleftrightarrow \frac{(x+2)^2}{x}-\left|\frac{(x-2)^2}{x}\right|\geq 8\left(\frac{x^2+1}{x}-\left|\frac{x^2-1}{x}\right|\right)$
  -- $\Longleftrightarrow \frac{8|x^2-1|-(x-2)^2}{|x|}\geq \frac{8(x^2+1)-(x+2)^2}{x}$
  -- $\Longleftrightarrow \frac{8|x^2-1|-(x-2)^2}{|x|}\geq \frac{7x^2-4x+4}{x}\
  -- \cdots [\*]$
  have hiff : min 4 (x + 4 / x) ≥ 8 * min x (1 / x) ↔ (8 * |x ^ 2 - 1| - (x - 2) ^ 2) / |x| ≥ (8 * (x ^ 2 + 1) - (x + 2) ^ 2) / x := by
    rw [hmin_eq, hmin_eq]
    trans (x + 2) ^ 2 / x - |(x - 2) ^ 2 / x| ≥ 8 * ((x ^ 2 + 1) / x - |(x ^ 2 - 1) / x|)
    · have : (x + 1 / x) / 2 = ((x ^ 2 + 1) / x) * (1 / 2) := by field_simp; ring
      rw [this]
      have : |x - 1 / x| / 2 =|(x ^ 2 - 1) / x| * (1 / 2) := by field_simp; congr 1; ring
      rw [this]
      have : (4 + (x + 4 / x)) / 2 = ((x + 2) ^ 2 / x) * (1 / 2) := by
        field_simp
        ring
      rw [this]
      have : |4 - (x + 4 / x)| / 2 = |(x - 2) ^ 2 / x| * (1 / 2) := by
        trans |(x + 4 / x) - 4| / 2
        · congr 1
          exact abs_sub_comm 4 (x + 4 / x)
        · field_simp
          congr 1
          ring
      rw [this]
      rw [←sub_mul, ←sub_mul, ←mul_assoc]
      simp
    · rw [mul_sub, abs_div, abs_div, sub_div, sub_div, abs_sq, ←mul_div_assoc, ←mul_div_assoc]
      constructor <;> intro h
      all_goals linear_combination h
  rw [hiff]
  -- Case 1: $x&gt;0$
  -- $[\*]\Longleftrightarrow \frac{8|x^2-1|-(x-2)^2}{x}\geq \frac{7x^2-4x+4}{x}$
  by_cases hx' : x > 0
  · simp [show ¬ x < 0 by push_neg; apply le_of_lt hx', abs_of_pos hx', hx']
    rw [div_le_div_iff_of_pos_right hx']
    constructor <;> intro h
    · have h : 1 - x + x ^ 2 ≤ |-1 + x ^ 2| := by
        have : 8 * (x ^ 2 + 1) - (x + 2) ^ 2 + (x - 2) ^ 2 ≤ 8 * |x ^ 2 - 1| := by linarith only [h]
        ring_nf at this
        linarith only [this]
      by_cases hx'' : x < 1
      · have : -1 + x ^ 2 < 0 := by nlinarith
        simp [abs_of_neg this] at h
        ring_nf at h
        left
        nlinarith
      · right
        have : -1 + x ^ 2 ≥ 0 := by nlinarith
        simp [abs_of_nonneg this] at h
        ring_nf at h
        nlinarith
    · suffices h : 8 * (x ^ 2 + 1) - (x + 2) ^ 2 + (x - 2) ^ 2 ≤ 8 * |x ^ 2 - 1|
      · linarith only [h]
      · ring_nf
        nth_rw 1 [show (8 : ℝ) = 1 * 8 by simp]
        rw [←sub_mul, ←add_mul]
        simp
        rcases h with h | h
        · have : -1 + x ^ 2 < 0 := by nlinarith
          simp [abs_of_neg this]
          ring_nf
          nlinarith
        · have : -1 + x ^ 2 ≥ 0 := by nlinarith
          simp [abs_of_nonneg this]
          ring_nf
          nlinarith
  · -- Case 2: $x&lt;0$
    simp at hx'
    have : |x| = -x := by exact abs_of_nonpos hx'
    have hx' : x < 0 := by exact lt_of_le_of_ne hx' hx
    simp [this, div_neg]
    -- $[\*]\Longleftrightarrow \frac{(x-2)^2-8|x^2-1|}{-x}\geq \frac{7x^2-4x+4}{x}$
    rw [neg_div', neg_sub]
    rw [div_le_div_right_of_neg hx']
    -- Since $x&lt;0$ , we have $8|x^2-1|-(x-2)^2\leq 7x^2-4x+4\Longleftrightarrow 8|x^2-1|\geq -6x^2$ , which holds for all real numbers $x$ .
    simp [hx']
    -- Thus in this case, the solution is $x&lt;0\ \cdots [2]$ .
    -- Therefore from $[1],\ [2]$ , the desired answer is $\boxed{x&lt;0\ or\ 0&lt;x\leq \frac 12\ or\ 2\leq x}$ 
    suffices h : (x - 2) ^ 2 + (x + 2) ^ 2 - 8 * (x ^ 2 + 1) ≤ 8 * |x ^ 2 - 1|
    · linarith only [h]
    · ring_nf
      trans 0
      · simp
        apply sq_nonneg
      · positivity