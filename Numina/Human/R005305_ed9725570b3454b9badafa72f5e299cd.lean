import Mathlib

/- Soit ( $a_{n}$ ) une suite définie par $a_{1}, a_{2} \in[0,100]$ et

$$
a_{n+1}=a_{n}+\frac{a_{n-1}}{n^{2}-1} \quad \text { pour tout enter } n \geqslant 2
$$

Existe-t-il un entier $n$ tel que $a_{n}>2013$ ?
$$ -/
theorem algebra_607512 (a : ℕ → ℝ) (ha0: a 0 ∈ Set.Icc 0 100) (ha1: a 1 ∈ Set.Icc 0 100)
  (ha: ∀ n, 2 ≤ n → a n = a (n - 1) + a (n - 2) / (n ^ 2 - 1)) :
  ¬ ∃ n, a n > 2013 := by
  simp
  intro N
  -- we want to prove that $a(n) ≤ 400$ for all n
  apply le_trans' (show (400:ℝ) ≤ 2013 by norm_num)
  -- using strong induction on n
  apply @Nat.strong_induction_on (fun n => a n ≤ 400) N
  intro n ihn
  -- if $n < 2$, we have $a_0 <= 100$ and $a_1 <= 100$
  by_cases hn : n < 2
  . by_cases hn': n = 0
    . rw [hn']
      simp at ha0
      linarith only [ha0.2]
    . rw [<-ne_eq, <-Nat.one_le_iff_ne_zero] at hn'
      have : n = 1 := by linarith
      rw [this]
      simp at ha1
      linarith only [ha1.2]
  simp at hn
  -- if $n >= 2$, we have $a_n = a_{n-1} + a_{n-2} / (n^2 - 1)$
  -- turn $a_n$ into a sum from $a_1$
  have h1 : a n = a 1 + ∑ i ∈ Finset.Icc 2 n, a (i - 2) / (i ^ 2 - 1) := by
    let k := n - 2
    have h1 : n = k + 2 := by simp [k]; rw [Nat.sub_add_cancel hn]
    rw [h1]
    induction k with
    | zero =>
      simp
      specialize ha 2 (by simp)
      simp at ha
      exact ha
    | succ k' ih =>
      rw [Finset.sum_Icc_succ_top, <-add_assoc, <-ih, show k' + 1 + 2 = k' + 3 by simp]
      simp
      specialize ha (k'+3) (by simp)
      simp at ha
      exact ha
      simp
  -- split the sum into two parts, the second part is bounded by $400 / (n^2 - 1)$ beacuse $a_i <= 400$ from the induction hypothesis
  have h2 : ∑ i ∈ Finset.Icc 2 n, a (i - 2) / (i ^ 2 - 1) ≤ ∑ i ∈ Finset.Icc 2 n, (400:ℝ) / (i ^ 2 - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    simp at hi
    have : i - 2 < n := by
      have : i - 1 < n := Nat.sub_one_lt_of_le (by linarith [hi.1]) hi.2
      apply lt_trans' this
      apply Nat.sub_one_lt
      simp
      intro i_eq_1
      replace i_eq_1:= Nat.le_of_sub_eq_zero i_eq_1
      linarith [hi.1]
    have h' := ihn (i-2) this
    rw [div_le_div_iff_of_pos_right]
    exact h'
    simp
    linarith only [hi.1]
  -- the sum is bounded by $200 * (1 + 1/2 - 1/n - 1/(n+1))$
  have h3 : ∑ i ∈ Finset.Icc 2 n, (400:ℝ) / (i ^ 2 - 1) = 200 * ((1:ℝ) + 1 / 2 - 1 / n - 1 / (n + 1)) := by
    let k := n - 2
    have h1 : n = k + 2 := by simp [k]; rw [Nat.sub_add_cancel hn]
    rw [h1]
    induction k with
    | zero =>
      simp
      ring_nf
    | succ k' ih =>
      rw [Finset.sum_Icc_succ_top, ih, Nat.cast_add, Nat.cast_add, Nat.cast_add]
      ring_nf
      have : (8 + (k':ℝ) * 6 + k' ^ 2)⁻¹ = 1 / 2 * (1 / ((k': ℝ) + 2) - 1 / (k' + 4)) := by
        rw [show 8 + (k':ℝ) * 6 + k' ^ 2 = (k' + 2) * (k' + 4) by ring]
        have: ((k':ℝ) + 2) * (k' + 4) ≠ 0 := by norm_cast; intro h; simp at h
        rw [<-mul_left_inj' this]
        rw [inv_mul_cancel₀ this, mul_sub, sub_mul, <-mul_assoc]
        conv =>
          rhs
          arg 1
          arg 1
          rw [mul_assoc]
        rw [div_mul_cancel₀]
        conv =>
          rhs
          arg 2
          conv => arg 2; rw [mul_comm]
          rw [<-mul_assoc]
          arg 1
          rw [mul_assoc]
        rw [div_mul_cancel₀]
        simp
        ring
        norm_cast
        norm_cast
      rw [this]
      ring_nf
      simp
  rw [h3] at h2
  -- add the two parts together
  have h4 : a n ≤ 100 + 200 * ((1:ℝ) + 1 / 2 - 1 / n - 1 / (n + 1)) := by
    rw [h1]
    simp at ha1
    linear_combination ha1.2 + h2
  apply le_trans h4
  -- so we need to prove that $100 + 200 * (1 + 1/2 - 1/n - 1/(n+1)) <= 400$
  -- which is equivalent to $0 <= 200 * (1/n + 1/(n+1))$
  -- that is obvious
  apply le_of_sub_nonneg
  ring_nf
  apply add_nonneg
  apply mul_nonneg
  simp
  simp
  apply mul_nonneg
  simp
  norm_cast
  simp
  simp
