import Mathlib

open Real

/- 10. For positive numbers $a, b, c$, the inequality $a+b+c \geqslant \sqrt[m+n+k]{a^{m} b^{n} c^{k}}+\sqrt[m+n+k]{a^{n} b^{k} c^{m}}+\sqrt[m+n+k]{a^{k} b^{m} c^{n}}$ holds. Prove it. -/
theorem inequalities_189973 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m n k : ℕ) (hm : m > 0) (hn : n > 0) (hk : k > 0) :
    a + b + c ≥ (a ^ m * b ^ n * c ^ k) ^ ((1 : ℝ) / (m + n + k)) +
    (a ^ n * b ^ k * c ^ m) ^ ((1 : ℝ) / (m + n + k)) +
    (a ^ k * b ^ m * c ^ n) ^ ((1 : ℝ) / (m + n + k)) := by

    -- define p := m + n + k
    let p : ℝ := m + n + k
    have p_pos : p > 0 := by positivity

    -- by AM-GM inequality, we have
    -- 1. $\sqrt[m + n + k]{a^m b^n c^k} ≤ (m/p)a + (n/p)b + (k/p)c$
    have h1 : (a ^ m * b ^ n * c ^ k) ^ ((1 : ℝ) / (m + n + k)) ≤
      (m / p) * a + (n / p) * b + (k / p) * c := by
        have : (a ^ m * b ^ n * c ^ k) ^ ((1 : ℝ) / (m + n + k)) =
          a ^ (m / p) * b ^ (n / p) * c ^ (k / p) := by
            rw [Real.mul_rpow, Real.mul_rpow]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            all_goals positivity
        rw [this]
        refine geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ ?_ ?_ ?_ ?_
        iterate 6 positivity
        unfold p
        field_simp

    -- 2. $\sqrt[m + n + k]{a^n b^k c^m} ≤ (n/p)a + (k/p)b + (m/p)c$
    have h2 : (a ^ n * b ^ k * c ^ m) ^ ((1 : ℝ) / (m + n + k)) ≤
      (n / p) * a + (k / p) * b + (m / p) * c := by
        have : (a ^ n * b ^ k * c ^ m) ^ ((1 : ℝ) / (m + n + k)) =
          a ^ (n / p) * b ^ (k / p) * c ^ (m / p) := by
            rw [Real.mul_rpow, Real.mul_rpow]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            all_goals positivity
        rw [this]
        refine geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ ?_ ?_ ?_ ?_
        iterate 6 positivity
        unfold p
        field_simp
        ring

    -- 3. $\sqrt[m + n + k]{a^k b^m c^n} ≤ (k/p)a + (m/p)b + (n/p)c$
    have h3 : (a ^ k * b ^ m * c ^ n) ^ ((1 : ℝ) / (m + n + k)) ≤
      (k / p) * a + (m / p) * b + (n / p) * c := by
        have : (a ^ k * b ^ m * c ^ n) ^ ((1 : ℝ) / (m + n + k)) =
          a ^ (k / p) * b ^ (m / p) * c ^ (n / p) := by
            rw [Real.mul_rpow, Real.mul_rpow]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            rw [← rpow_natCast, ← rpow_mul, mul_one_div]
            all_goals positivity
        rw [this]
        refine geom_mean_le_arith_mean3_weighted ?_ ?_ ?_ ?_ ?_ ?_ ?_
        iterate 6 positivity
        unfold p
        field_simp
        ring

    -- summing the above inequalities we get the answer
    have h4 : (a ^ m * b ^ n * c ^ k) ^ ((1 : ℝ) / (m + n + k)) +
      (a ^ n * b ^ k * c ^ m) ^ ((1 : ℝ) / (m + n + k)) +
      (a ^ k * b ^ m * c ^ n) ^ ((1 : ℝ) / (m + n + k)) ≤
      (m / p) * a + (n / p) * b + (k / p) * c +
      (n / p) * a + (k / p) * b + (m / p) * c +
      (k / p) * a + (m / p) * b + (n / p) * c := by
        linarith only [h1, h2, h3]

    have h5 : (m / p) * a + (n / p) * b + (k / p) * c +
      (n / p) * a + (k / p) * b + (m / p) * c +
      (k / p) * a + (m / p) * b + (n / p) * c = a + b + c := by
        field_simp
        ring

    linarith only [h4, h5]
