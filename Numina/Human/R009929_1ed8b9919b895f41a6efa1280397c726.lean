import Mathlib

/- When a student multiplied the number 66 by the repeating decimal
1.abab... = 1.\overline{ab}
where a and b are digits, he did not notice the notation and just multiplied 66 times 1.ab. Later he found that his answer is 0.5 less than the correct answer. What is the 2-digit number ab?
(A) 15
(B) 30
(C) 45
(D) 60
(E) 75
(A) 15(B) 30(C) 45(D) 60(E) 75 -/
theorem algebra_94221 {a b : ℕ} (ha : a < 10) (hb : b < 10) (h : 66 * (1 + ∑' n: ℕ, (a / (10:ℝ)^(2*n+1)) + (∑' n: ℕ, b / (10:ℝ)^(2*n+2))) = 66 * (1 + a/(10:ℝ) + b/(100:ℝ)) - 0.5) : 10 * a + b = 75 := by
  -- a leema to be used later
  have aux (n: ℕ) : (100:ℝ)^(n:ℝ) = (10:ℝ)^((n:ℝ) * 2) := by
    calc
      (100:ℝ)^(n:ℝ) = ((10:ℝ)^2)^(n:ℝ) := by norm_num
      _ = ((10:ℝ)^(2:ℝ))^(n:ℝ) := by norm_cast
      _ = (10:ℝ)^((2:ℝ) * n) := by rw [Real.rpow_mul (by norm_num) 2 n]
      _ = (10:ℝ)^((n:ℝ) * 2) := by ring_nf
  -- first express the terms inside sums as constant times a geometric term
  have aux' (n: ℕ) : a / (10:ℝ)^(2*n+1) = (a / (10:ℝ)) • (1 / (100:ℝ))^n := by
    field_simp; left; ring_nf; simp;
    have := aux n
    norm_cast at this; norm_cast
  have aux'' (n: ℕ) : b / (10:ℝ)^(2*n+2) = (b / (100:ℝ)) • (1 / (100:ℝ))^n := by
    field_simp; left; ring_nf; simp
    have := aux n
    norm_cast at this; norm_cast
  -- rewrite at h and rewrite wtih geometric series value
  simp_rw [aux', aux''] at h
  rw [tsum_const_smul _ (summable_geometric_of_norm_lt_one (by norm_num))] at h
  rw [tsum_const_smul _ (summable_geometric_of_norm_lt_one (by norm_num))] at h
  rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)] at h
  -- simplify the numbers and then solve by linear arithmetic
  norm_num at h
  have h' : 1 + a / (10:ℝ) * (100 / 99) + (b:ℝ) / 100 * (100 / 99) = (99 + 10 * a + b) / (99:ℝ) := by
    ring
  have h'' : 1 + a / (10:ℝ) + (b:ℝ) / 100 = (100 + 10 * a + b) / (100:ℝ) := by
    ring
  rw [h', h''] at h
  rify
  linarith