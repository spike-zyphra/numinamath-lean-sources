import Mathlib 

/- Suppose that  $y$  is a positive integer written only with digit  $1$ ,
 in base  $9$  system. Prove that  $y$  is a triangular number, that is,
  exists positive integer  $n$  such that the number  $y$  is the sum of
  the  $n$  natural numbers from  $1$  to  $n$ .-/
theorem number_theory_8759 (y k : ℕ) 
-- A number made up entirely of \( k \) digits of \( 1 \) in base \( 9 \) can be written as:
  -- \[
  -- y = 1 + 1 \cdot 9 + 1 \cdot 9^2 + \cdots + 1 \cdot 9^{k-1} = \frac{9^k - 1}{8}
  -- \]
(h : y = ∑ i in Finset.range k, 9^i) :
  ∃ n, y =  ∑ i in Finset.range n, (i + 1) := by
    have h1 : ∀ k, ∑ i in Finset.range k, 9^i = (9 ^ k - 1) / 8 :=
      Nat.geomSum_eq (by simp)
    -- A triangular number is of the form:
    -- \[
    -- T_n = \frac{n(n+1)}{2}
    -- \]
    -- for some positive integer \( n \).
    have h2 : ∀ n, ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
      intro n 
      refine Nat.eq_div_of_mul_eq_right (by simp) ?h
      rw [Finset.sum_add_distrib, mul_add, mul_comm, Finset.sum_range_id_mul_two] 
      simp [Nat.mul_sub, mul_add]
      rw [←Nat.sub_add_comm]
      omega
      nlinarith
    -- an auxiliary lemma : $n \mid (n+1)^ k$ where n is arbitrary integer.
    have aux : ∀ n, (n + 1)^k ≡ 1 [ZMOD n] := by 
      intro n 
      nth_rw 2 [show (1 : ℤ) = 1^k by simp]
      exact Int.ModEq.pow k (by simp)
    -- for each \( k \), there exists a positive integer \( n = \frac{3^k - 1}{2} \) such that
    -- \( y \) is the \( n \)-th triangular number.
    have h3 : (3^k - 1) / 2 * ((3^k - 1) / 2 + 1) / 2 = (9 ^ k - 1) / 8 := by
      zify
      simp
      rify
      rw [Int.cast_div (hn := by simp), Int.cast_div (hn := by simp)]
      simp only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_ofNat, Int.cast_sub,
        Int.cast_pow]
      rw [Int.cast_div (hn := by simp)]
      field_simp
      ring_nf
      congr 2
      rw [mul_comm, pow_mul]
      norm_num
      exact Int.ModEq.dvd <| (aux 2).symm
      exact Int.ModEq.dvd <| (aux 8).symm
      have := Int.even_mul_succ_self <| (3 ^ k - 1) / 2
      exact even_iff_two_dvd.mp this
    use (3^k - 1) / 2
    rw [h2 ((3^k - 1) / 2 ), h, h1 k]
    exact h3.symm