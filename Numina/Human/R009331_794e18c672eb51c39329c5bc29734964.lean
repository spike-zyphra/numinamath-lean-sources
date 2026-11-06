import Mathlib

open Finset Real

/- Example 5 (24th All-Soviet Union Middle School Mathematics Competition Problem) Prove: For positive numbers $a_{1}, a_{2}, \cdots, a_{n}$ whose sum is 1, the inequality $\frac{a_{1}^{2}}{a_{1}+a_{2}}+\frac{a_{2}^{2}}{a_{2}+a_{3}}+\cdots+\frac{a_{n-1}^{2}}{a_{n-1}+a_{n}}+\frac{a_{n}^{2}}{a_{n}+a_{1}} \geqslant \frac{1}{2}$ holds. -/
theorem inequalities_276965 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∑ i ∈ range n, a i = 1) (ha' : ∀ i ∈ range n, 0 < a i) :
    ∑ i ∈ range n, (a i)^2 / (a i + a ((i + 1) % n)) ≥ 1 / 2 := by
  -- let A be the sum from the theorem statement
  set A := ∑ i ∈ _, (_ : ℝ)
  -- let B be the conjugate of A
  set B := ∑ i ∈ range n, (a ((i + 1) % n))^2 / (a i + a ((i + 1) % n))
  have ha1 {i} (hi : i ∈ range n) : 0 < a ((i + 1) % n) := by
    apply ha'
    simp [Nat.mod_lt (i + 1) hn]
  have hd {i} (hi : i ∈ range n) : 0 < a i + a ((i + 1) % n) := by linarith [ha' _ hi, ha1 hi]
  -- show that ∑ i, a((i + 1) % n) = ∑ i, a(i)
  have hsum : ∑ i ∈ range n, a ((i + 1) % n) = ∑ i ∈ range n, a i := by
    nth_rw 1 3 [show n = (n - 1) + 1 by omega]
    rw [sum_range_succ, sum_range_succ']
    congrm ?_ + a (?_)
    · apply sum_congr rfl
      simp
      intro i hi
      congr
      apply Nat.mod_eq_of_lt
      omega
    · simp [show n - 1 + 1 = n by omega]
  -- prove that A = B by showing that A - B = 0
  have eq : A - B = 0 := calc
    A - B = ∑ i ∈ range n, ((a i)^2 - (a ((i + 1) % n))^2) / (a i + a ((i + 1) % n)) := by
      simp_rw [A, B, ←sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      field_simp [ne_of_gt (hd hi)]
    _ = ∑ i ∈ range n, (a i - a ((i + 1) % n)) := by
      apply sum_congr rfl
      intro i hi
      field_simp [ne_of_gt (hd hi)]
      ring
    _ = 0 := by rw [sum_sub_distrib, hsum, sub_self]
  calc
    -- A = B implies that A = (A + B) / 2
    A = (A + B) / 2 := by linarith
    _ = ∑ i ∈ range n, 1 / 2 * ((a i)^2 + a ((i + 1) % n)^2) / (a i + a ((i + 1) % n)) := by
      simp_rw [A, B, ←sum_add_distrib, sum_div]
      apply sum_congr rfl
      intro i hi
      field_simp [ne_of_gt (hd hi)]
      left
      ring
    -- we have x ^ 2 + y ^ 2 ≥ 1 / 2 * (x + y)^2 for all x, y
    _ ≥ ∑ i ∈ range n, 1 / 2 * ((a i + a ((i + 1) % n))^2 / 2) / (a i + a ((i + 1) % n)) := by
      apply sum_le_sum
      intro i hi
      apply (div_le_div_iff_of_pos_right (hd hi)).mpr
      rw [mul_le_mul_left (by norm_num)]
      linarith [two_mul_le_add_pow_two (a i) (a ((i + 1) % n))]
    _ = 1 / 4 * ∑ i ∈ range n, (a i + a ((i + 1) % n)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      field_simp [ne_of_gt (hd hi)]
      ring
    -- the final equality follows from the condition ∑ i, a i = 1
    _ = 1 / 2 := by
      rw [sum_add_distrib, hsum, ha]
      norm_num