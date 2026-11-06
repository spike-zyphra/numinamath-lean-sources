import Mathlib

-- Tim starts with a number \( n \), then repeatedly flips a fair coin. If it lands heads he subtracts 1 from his number and if it lands tails he subtracts 2. Let \( E_n \) be the expected number of flips Tim does before his number is zero or negative. Find the pair \( (a, b) \) such that \[\lim_{n \to \infty} (E_n - an - b) = 0\]
theorem algebra_609545 (E : ℕ → ℝ)(h : ∀ n ≥ 2, E n = 1/2 * (E (n-1) + 1) + 1/2 * (E (n-2) + 1))(hE0 : E 0 = 0)(hE1 : E 1 = 1): ∀ ε > 0, ∃ N, ∀ n > N, |E n - (2/3*n + 2/9)| < ε := by
  -- Establish the formula for \( E_n \) using strong induction
  have hEn : ∀ n, E n = 2/3*n + 2/9 - 2/9*(-1/2)^n := by
    intro n
    let p : ℕ → Prop := fun n => E n = 2/3*n + 2/9 - 2/9*(-1/2)^n
    apply @Nat.strong_induction_on p
    intro n hn
    by_cases hzero : n = 0
    · -- Base case for n = 0
      rw [hzero]
      unfold p
      simp
      rw [hE0]
    · by_cases hone : n = 1
      · -- Base case for n = 1
        rw [hone]
        unfold p
        simp
        rw [hE1]
        norm_num
      · -- Inductive step for n ≥ 2
        have hpos : n > 0 := by exact Nat.zero_lt_of_ne_zero hzero
        have hge : n ≥ 2 := by
          apply (Nat.two_le_iff n).mpr
          simp
          exact ⟨hzero, hone⟩
        unfold p
        rw [h n hge]
        have hn1 := hn (n-1) (by exact Nat.sub_one_lt_of_lt hge)
        rw [hn1]
        have hlt : n-2 < n := by
          refine Nat.sub_lt hpos ?_
          norm_num
        have hn2 := hn (n-2) hlt
        rw [hn2]
        have : (-(1:ℝ)/2) = - (1/2) := by norm_num
        rw [this]
        have heq1 : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hzero
        have heq2 : n - 2 + 2 = n := by apply Nat.sub_add_cancel hge
        have heq3 : n-2 + 1 = n-1 := by
          exact Eq.symm ((fun {m n} => Nat.pred_eq_succ_iff.mpr) (id (Eq.symm heq2)))
        have h1 : (-((1:ℝ)/2)) ^ n = (-((1:ℝ)/2)) ^ (n-2) * 1/4 := by
          nth_rw 1 [← heq2]
          rw [npow_add]
          ring_nf
        have h2 : (-((1:ℝ)/2)) ^ (n-1) = (-(1:ℝ)/2) ^ (n-2) * (-1/2) := by
          nth_rw 1 [← heq3]
          rw [npow_add]
          ring_nf
        rw [h1, h2]
        ring_nf
        have : (((n-1) : ℕ) : ℝ) = n - 1 := by apply Nat.cast_pred hpos
        have h3 : ((n-1):ℕ) * ((1:ℝ)/3) = n * 1/3 - 1/3 := by
          rw [this]
          ring
        have : (((n-2) : ℕ) : ℝ) = n - 2 := by
          refine EReal.coe_eq_coe_iff.mp ?_
          norm_cast
        have h4 : ((n-2):ℕ) * ((1:ℝ)/3) = n * 1/3 - 2/3 := by
          rw [this]
          ring
        rw [h3, h4]
        ring_nf
  -- Prove the limit using epsilon-delta definition
  intro ε hε
  let M := Real.logb ((1:ℝ)/2) (ε/2)
  have : ∃ N : ℕ, N > M := by exact exists_nat_gt M
  rcases this with ⟨N, hN⟩
  use N
  intro n hn
  rw [hEn]
  simp
  rw [abs_mul]
  norm_num
  have : |(2:ℝ)/9| = 2/9 := by norm_num
  rw [this]
  have : |(1:ℝ)/2| = 1/2 := by norm_num
  rw [this]
  have lt: (1 / 2) ^ n < ε := by
    calc
      _ ≤ ((1:ℝ)/2) ^ N := by
        have := @Real.rpow_le_rpow_of_exponent_ge' ((1:ℝ)/2) n N (by linarith) (by linarith) (by linarith) (by norm_cast;linarith)
        norm_cast at this
      _ ≤ (1/2) ^ M := by
        have := @Real.rpow_le_rpow_of_exponent_ge_of_imp ((1:ℝ)/2) N M (by linarith) (by linarith) (by linarith) (by intro hfalse;norm_num at hfalse)
        norm_cast at this
      _ < _ := by
        unfold M
        have : (1 / 2) ^ Real.logb (1 / 2) (ε / 2) = ε/2 := by apply Real.rpow_logb (by linarith) (by norm_num) (by linarith)
        rw [this]
        linarith
  linarith
