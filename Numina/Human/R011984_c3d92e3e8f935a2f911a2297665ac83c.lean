import Mathlib

/- 10.17 A sequence is recursively defined as: $t_{1}=1$, for $n>1$, when $n$ is even, $t_{n}=1+t \frac{n}{2}$; when $n$ is odd, $t_{n}=\frac{1}{t_{n-1}}$. If it is known that $t_{n}=\frac{19}{87}$, then the sum of the digits of $n$ is
(A) 15.
(B) 17.
(C) 19.
(D) 21.
(E) 23.
(38th American High School Mathematics Examination, 1987) -/
theorem algebra_164075 {t : ℕ → ℝ} (ht1 : t 1 = 1) (hht : ∀ n > 1, Even n → t n = 1 + t (n / 2)) (hht' : ∀ n > 1, Odd n → t n = 1 / t (n - 1)) : ∃ n , t n = 19 / 87 ∧ (Nat.digits 10 n).sum = 15 := by
--We prove that 1905 satisfies t n = 19 / 87 and then compute the sum of its digits. To do so, we backtrack the sequence t starting from n = 1905.
  use 1905
  have h1905 := hht' 1905
  have odd1905 : Odd 1905 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, odd1905, Nat.add_one_sub_one, forall_const] at h1905
  have h1904 := hht 1904
  have even1904 : Even 1904 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even1904, Nat.reduceDiv, forall_const] at h1904
  have h952 := hht 952
  have even952 : Even 952 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even952, Nat.reduceDiv, forall_const] at h952
  have h476 := hht 476
  have even476 : Even 476 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even476, Nat.reduceDiv, forall_const] at h476
  have h238 := hht 238
  have even238 : Even 238 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even238, Nat.reduceDiv, forall_const] at h238
  have h119 := hht' 119
  have odd119 : Odd 119 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, odd119, Nat.add_one_sub_one, forall_const] at h119
  have h118 := hht 118
  have even118 : Even 118 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even118, Nat.reduceDiv, forall_const] at h118
  have h59 := hht' 59
  have odd59 : Odd 59 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, odd59, Nat.add_one_sub_one, forall_const] at h59
  have h58 := hht 58
  have even58 : Even 58 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even58, Nat.reduceDiv, forall_const] at h58
  have h29 := hht' 29
  have odd29 : Odd 29 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, odd29, Nat.add_one_sub_one, forall_const] at h29
  have h28 := hht 28
  have even28 : Even 28 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even28, Nat.reduceDiv, forall_const] at h28
  have h14 := hht 14
  have even14 : Even 14 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even14, Nat.reduceDiv, forall_const] at h14
  have h7 := hht' 7
  have odd7 : Odd 7 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, odd7, Nat.add_one_sub_one, forall_const] at h7
  have h6 := hht 6
  have even6 : Even 6 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even6, Nat.reduceDiv, forall_const] at h6
  have h3 := hht' 3
  have odd3 : Odd 3 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, odd3, Nat.add_one_sub_one, forall_const] at h3
  have h2 := hht 2
  have even2 : Even 2 := by decide
  simp only [gt_iff_lt, Nat.one_lt_ofNat, even2, Nat.reduceDiv, forall_const] at h2
--Now that we have arrived at t 2 = 2, we compute the terms t n for n = 1, 3, 6, 7, 14, 28, 29, 58, 59, 118, 119, 238, 476, 952, 1904, and 1905.
  rw [ht1] at h2
  ring_nf at h2
  rw [h2] at h3
  rw [h3] at h6
  ring_nf at h6
  rw [h6] at h7
  ring_nf at h7
  rw [h7] at h14
  ring_nf at h14
  rw [h14] at h28
  ring_nf at h28
  rw [h28] at h29
  ring_nf at h29
  rw [h29] at h58
  ring_nf at h58
  rw [h58] at h59
  ring_nf at h59
  rw [h59] at h118
  ring_nf at h118
  rw [h118] at h119
  ring_nf at h119
  rw [h119] at h238
  ring_nf at h238
  rw [h238] at h476
  ring_nf at h476
  rw [h476] at h952
  ring_nf at h952
  rw [h952] at h1904
  ring_nf at h1904
  rw [h1904] at h1905
  ring_nf at h1905
--We are ready to prove the two properties.
  constructor
  · exact h1905
  · native_decide