import Mathlib

/-Compute $i+i^2+i^3+\cdots+i^{258}+i^{259}$.-/
theorem algebra_21287 : ∑ i ∈ Finset.range 259, (Complex.I : ℂ) ^ (i + 1) = -1 := by
  -- show that i + i ^ 2 + i ^ 3 + i ^ 4 = 0
  have eq4 : ∑ i ∈ Finset.range 4, (Complex.I) ^ (i + 1) = 0 := by
    simp [Finset.sum]
    ring_nf
    calc
      Complex.I + Complex.I ^ 3 = Complex.I + Complex.I ^ 2 * Complex.I := by ring_nf
      _ = Complex.I + (-1) * Complex.I := by simp
      _ = 0 := by ring_nf
  -- show that ∑ i ∈ Finset.range m, I ^ (i + 1) = ∑ i ∈ Finset.range (m - 4 * n), I ^ (i + 1 + 4 * n) (when 4 * n ≤ m)
  have eqmn (m n : ℕ) (hmn : 4 * n ≤ m) : ∑ i ∈ Finset.range m, Complex.I ^ (i + 1) = ∑ i ∈ Finset.range (m - 4 * n), Complex.I ^ (i + 1 + 4 * n) := by
    -- prove by induction
    induction n with
    -- when n = 0
    | zero =>
      congr
    -- when n satisfied, show the case of n + 1
    | succ n hn =>
      replace hn : ∑ i ∈ Finset.range m, Complex.I ^ (i + 1) = ∑ i ∈ Finset.range (m - 4 * n), Complex.I ^ (i + 1 + 4 * n) := by
        apply hn
        linarith only [hmn]
      -- extract the first four terms
      calc
        ∑ i ∈ Finset.range m, Complex.I ^ (i + 1) = ∑ i ∈ Finset.range (m - 4 * n), Complex.I ^ (i + 1 + 4 * n) := by rw [hn]
        _ = ∑ i ∈ Finset.range (4 + (m - 4 * (n + 1))), Complex.I ^ (i + 1 + 4 * n) := by congr; ring_nf; rw [<-Nat.add_sub_assoc, Nat.add_sub_add_left]; linarith only [hmn]
        _ = ∑ i ∈ Finset.range 4, Complex.I ^ (i + 1 + 4 * n) + ∑ i ∈ Finset.range (m - 4 * (n + 1)), Complex.I ^ (4 + i + 1 + 4 * n) := by apply Finset.sum_range_add
        _ = ∑ i ∈ Finset.range 4, Complex.I ^ (i + 1) * (Complex.I) ^ (4 * n) + ∑ i ∈ Finset.range (m - 4 * (n + 1)), Complex.I ^ (4 + i + 1 + 4 * n) := by congr; ring_nf; symm; ring_nf
        _ = (∑ i ∈ Finset.range 4, Complex.I ^ (i + 1)) * (Complex.I) ^ (4 * n) + ∑ i ∈ Finset.range (m - 4 * (n + 1)), Complex.I ^ (4 + i + 1 + 4 * n) := by rw [Finset.sum_mul]
        _ = ∑ i ∈ Finset.range (m - 4 * (n + 1)), Complex.I ^ (i + 1 + 4 * (n + 1)) := by rw [eq4]; norm_num; congr; ring_nf; symm; ring_nf
  -- rewrite by eqmn with m = 259 and n = 64
  rw [eqmn 259 64 (show 4 * 64 ≤ 259 by norm_num)]
  norm_num
  simp [Finset.sum]
  -- calculate the Complex.I ^ 259 + (Complex.I ^ 258 + Complex.I ^ 257)
  calc
    Complex.I ^ 259 + (Complex.I ^ 258 + Complex.I ^ 257) = (Complex.I ^ 2) ^ 129 * Complex.I + ((Complex.I ^ 2) ^ 129 + (Complex.I ^ 2) ^ 128 * Complex.I) := by ring_nf
    _ = (-1) ^ 129 * Complex.I + ((-1) ^ 129 + (-1) ^ 128 * Complex.I) := by norm_num
    _ = (-1) * Complex.I + (-1 + Complex.I) := by norm_num
    _ = -1 := by norm_num
