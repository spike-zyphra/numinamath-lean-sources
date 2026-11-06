import Mathlib

/- There are positive integers $x$ and $y$ that satisfy the system of equations
\begin{align*} \log_{10} x + 2 \log_{10} (\text{gcd}(x,y)) &= 60\\ \log_{10} y + 2 \log_{10} (\text{lcm}(x,y)) &= 570. \end{align*}
Let $m$ be the number of (not necessarily distinct) prime factors in the prime factorization of $x$, and let $n$ be the number of (not necessarily distinct) prime factors in the prime factorization of $y$. Find $3m+2n$. -/

theorem number_theory_97837 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h₁ : Real.logb 10 x + 2 * Real.logb 10 (Nat.gcd x y) = 60)
    (h₂ : Real.logb 10 y + 2 * Real.logb 10 (Nat.lcm x y) = 570) :
    3 * x.primeFactorsList.length + 2 * y.primeFactorsList.length = 880 := by
    -- basic assumptions about 10 = 2*5, x ≠ 0, etc.
    have primeFactorsList10 : Multiset.ofList [2,5] = Multiset.ofList (Nat.primeFactorsList 10) := by
      rw [Multiset.coe_eq_coe]
      apply Nat.primeFactorsList_unique
      norm_num
      intro p pmem
      fin_cases pmem
      <;> norm_num
    have factors_10 {k : ℕ} : (10).factorization.sum (fun _ e => k*e) = 2*k := by
      rw [Nat.factorization_eq_primeFactorsList_multiset]
      rw [<-primeFactorsList10]
      rw [Finsupp.sum]
      simp
      ring
    have x_ne_zero : x ≠ 0 := by linarith
    have y_ne_zero : y ≠ 0 := by linarith
    have x_gcd_y_ge_zero : x.gcd y > 0 := by
      apply Nat.gcd_pos_of_pos_left
      linarith
    have x_gcd_y_ne_zero : x.gcd y ≠ 0 := by
      exact Nat.gcd_ne_zero_left x_ne_zero
    -- compute log(x*y) by adding together the two equations and simplifying using logarithm rules
    have logxmuly : Real.logb 10 (x*y) = 210 := by
      calc
        Real.logb 10 (x*y) = Real.logb 10 x + Real.logb 10 y := by
          rw [Real.logb_mul]
          repeat (simp [*])
        _ = (Real.logb 10 x + 2 * Real.logb 10 (Nat.gcd x y) + Real.logb 10 y + 2 * Real.logb 10 (Nat.lcm x y))/3 := by
          rw [Nat.lcm]
          rw [Nat.cast_div]
          rw [Real.logb_div]
          rw [Nat.cast_mul]
          rw [Real.logb_mul]
          ring_nf
          repeat (simp [*])
          apply dvd_mul_of_dvd_right
          apply Nat.gcd_dvd_right
          simp [*]
        _ = 210 := by
          rw [h₁, add_assoc, h₂]
          norm_num
    -- compute x*y from log(x*y)
    have xmuly : x*y = 10^210 := by
      rw [<-@Nat.cast_inj ℝ]
      have onele10 : 1 < (10: ℝ) := by norm_num
      apply Real.logb_injOn_pos onele10
      simp
      apply mul_pos
      simp [*]
      simp [*]
      simp [*]
      rw [Nat.cast_pow, Real.logb_pow]
      simp [*]
    -- compute x * gcd(x,y)^2 from the first equation
    have xmulgcd : x * (Nat.gcd x y)^2 = 10^60 := by
      rw [<-@Nat.cast_inj ℝ]
      have onele10 : 1 < (10: ℝ) := by norm_num
      apply Real.logb_injOn_pos onele10
      simp
      apply mul_pos
      simp [*]
      apply Real.lt_sq_of_sqrt_lt
      simp [*]
      simp
      rw [Nat.cast_mul]
      rw [Real.logb_mul]
      rw [Nat.cast_pow]
      rw [Real.logb_pow]
      rw [Nat.cast_pow]
      rw [Real.logb_pow]
      norm_num
      exact h₁
      repeat simp [*]
    -- use how factorization interacts with multiplication and gcd to show that
    -- the two calculations above produce a contradicion if x > y
    have x_le_y {p : ℕ} (b :(10).factorization p ≠ 0) : x.factorization p ≤ y.factorization p := by
      by_contra
      have : x.factorization p ≤ 60*(10).factorization p := by
        calc
          x.factorization p ≤ (x * x.gcd y ^ 2).factorization p := by
            rw [Nat.factorization_mul, Nat.factorization_pow]
            rw [Nat.factorization_gcd]
            simp
            repeat linarith
            refine pow_ne_zero 2 ?_
            assumption
          _ = 60*(10).factorization p := by
            rw [xmulgcd]
            rw [Nat.factorization_pow]
            simp
        rfl
      have : 2*x.factorization p ≥ 210*(10).factorization p := by
        calc
          2*x.factorization p ≥ (x*y).factorization p := by
            rw [Nat.factorization_mul]
            simp
            linarith
            repeat assumption
          _ = 210*(10).factorization p := by
            rw [xmuly]
            rw [Nat.factorization_pow]
            simp
        rfl
      omega
    -- if p is not a factor of 10, it is not a factor of x or y
    have ten_p_zero {p : ℕ} (h : (10).factorization p = 0) : y.factorization p = x.factorization p := by
      have blah : (x.factorization p) + (y.factorization p) ≤ 0 := by
        rw [<-Finsupp.add_apply]
        rw [<-Nat.factorization_mul]
        rw [xmuly]
        rw [Nat.factorization_pow]
        simp
        exact h
        repeat linarith
      omega
    -- use how factorization interacts with gcd and the above proofs to show gcd x y = x
    have gcd_eq_x : Nat.gcd x y = x := by
      apply Nat.eq_of_factorization_eq
      assumption
      assumption
      intro p
      rw [Nat.factorization_gcd]
      by_cases xp : x.factorization p = 0
      simp [xp]
      rw [Finsupp.inf_apply]
      simp
      by_cases p_not_fac : (10).factorization p = 0
      have : y.factorization p = x.factorization p := by apply ten_p_zero p_not_fac
      linarith
      apply x_le_y p_not_fac
      repeat linarith
    -- combine gcd x y = x with the first equation to get a specific value for x
    have x_fac : x.factorization = (10^20).factorization := by
      apply Finsupp.ext
      intro p
      have : 3*x.factorization p = 3*(10 ^ 20).factorization p := by
        calc
          3*x.factorization p = (x^3).factorization p := by
            rw [Nat.factorization_pow]
            simp
          _ = (x*x.gcd y ^ 2).factorization p := by
            rw [gcd_eq_x]
            ring_nf
          _ = (10^60).factorization p := by
            rw [xmulgcd]
          _ = ((10^20)^3).factorization p := by
            simp
          _ = 3*(10 ^ 20).factorization p := by
            rw [Nat.factorization_pow]
            simp
        rfl
      linarith
    -- finish the final calculation using our calculated result for x*y and for x
    calc
      _ = (x.factorization.sum fun x ↦ id) + 2 * (x*y).factorization.sum fun x ↦ id := by
        repeat rw [<-Multiset.coe_card, <-Multiset.toFinsupp_sum_eq, <- Nat.factorization_eq_primeFactorsList_multiset]
        rw [Nat.factorization_mul]
        rw [Finsupp.sum_add_index]
        ring_nf
        repeat simp [*]
      _ = 880 := by
        rw [x_fac]
        rw [xmuly]
        repeat rw [Nat.factorization_pow]
        simp [Finsupp.sum_smul_index, factors_10]