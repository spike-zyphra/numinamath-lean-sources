import Mathlib

/-If a,b,c > 0, what is the smallest possible value of ⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋-/
theorem algebra_611307 {a b c: ℝ} (ha: 0 < a) (hb: 0 < b) (hc: 0 < c):
⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ ≥ 4 ∧ (∃ x y z: ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  ⌊(x + y) / z⌋ +  ⌊(y + z) / x⌋ +  ⌊(z + x) / y⌋ = 4) := by
  constructor
  -- Prove the first part of the theorem: the lower bound --
  . have ineq1:  ⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ > (a/b + b/a) + (b/c + c/b) + (c/a + a/c) - 3 := by
      calc
        ⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ > ((a + b)/c - 1) + ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ := by simp
                                                    _ > ((a + b)/c - 1) + ((b + c)/a - 1) + ⌊(c + a) / b⌋ := by simp
                                                    _ > ((a + b)/c - 1) + ((b + c)/a - 1) + ((c + a)/b - 1) := by simp
                                                    _ = (a/b + b/a) + (b/c + c/b) + (c/a + a/c) - 3 := by field_simp;ring_nf
    have ineq_ab: a/b + b/a ≥ 2 := by
      have eq_ab: a/b + b/a = (a - b) ^2 / (a * b) + 2 := by field_simp;ring_nf
      rw [eq_ab]
      simp
      have h1: 0 ≤ (a - b) ^2 := by nlinarith
      have h2: 0 ≤ a * b := by nlinarith
      exact div_nonneg h1 h2
    have ineq_bc: b/c + c/b ≥ 2 := by
      have eq_bc: b/c + c/b = (b - c) ^2 / (b * c) + 2 := by field_simp;ring_nf
      rw [eq_bc]
      simp
      have h1: 0 ≤ (b - c) ^2 := by nlinarith
      have h2: 0 ≤ b * c := by nlinarith
      exact div_nonneg h1 h2
    have ineq_ca: c/a + a/c ≥ 2 := by
      have eq_ca: c/a + a/c = (c - a) ^2 / (c * a) + 2 := by field_simp;ring_nf
      rw [eq_ca]
      simp
      have h1: 0 ≤ (c - a) ^2 := by nlinarith
      have h2: 0 ≤ c * a := by nlinarith
      exact div_nonneg h1 h2
    have ineq2: ⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ > 3 := by
      have o: ⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ > (3: ℝ) := by
        calc
          ⌊(a + b) / c⌋ +  ⌊(b + c) / a⌋ +  ⌊(c + a) / b⌋ > (a/b + b/a) + (b/c + c/b) + (c/a + a/c) - 3 := by exact ineq1
                                                      _ ≥ 2 + 2 + 2 - 3 := by nlinarith
                                                      _ = 3 := by norm_num
      norm_cast at o
    omega

  -- Prove the second part of the theorem: the existence of x, y, z --
  . use 6
    use 8
    use 9
    norm_num
