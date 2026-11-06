import Mathlib

-- Lemma which show that 2 < √5 ≤ 3.
lemma bound_sqrt_5 : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  refine ⟨?_, ?_⟩
  . rw [Real.lt_sqrt]
    <;> norm_num
  . rw [Real.sqrt_lt]
    <;> norm_num

-- Lemma which shows that (2 + √5) ^ (n + 2) = 4 * (2 + √5) ^ (n + 1) + (2 + √5) ^ n.
lemma iter_term_p (n : ℕ) : (2 + Real.sqrt 5) ^ (n + 2) = 4 * (2 + Real.sqrt 5) ^ (n + 1) + (2 + Real.sqrt 5) ^ n := by
  suffices (2 + Real.sqrt 5) ^ 2 = 4 * (2 + Real.sqrt 5) + 1 by
    rw [<-mul_left_inj' (show (2 + Real.sqrt 5) ^ n ≠ 0 by simp [show 2 + Real.sqrt 5 ≠ 0 by positivity]), <-pow_add, add_comm (2 : ℕ), add_mul, mul_assoc, <-pow_succ', one_mul] at this
    exact this
  rw [add_sq]
  field_simp
  ring

-- Lemma which shows that (2 - √5) ^ (n + 2) = 4 * (2 - √5) ^ (n + 1) + (2 - √5) ^ n.
lemma iter_term_m (n : ℕ) : (2 - Real.sqrt 5) ^ (n + 2) = 4 * (2 - Real.sqrt 5) ^ (n + 1) + (2 - Real.sqrt 5) ^ n := by
  suffices (2 - Real.sqrt 5) ^ 2 = 4 * (2 - Real.sqrt 5) + 1 by
    rw [<-mul_left_inj' (show (2 - Real.sqrt 5) ^ n ≠ 0 by simp [show 2 - Real.sqrt 5 ≠ 0 by linarith [bound_sqrt_5]]), <-pow_add, add_comm (2 : ℕ), add_mul, mul_assoc, <-pow_succ', one_mul] at this
    exact this
  rw [sub_sq]
  field_simp
  ring

-- Lemma which shows that (2 + √5) ^ n + (2 - √5) ^ n is natural number for any n.
lemma sum_is_nat (N : ℕ) : ∀ n ≤ N, ∃ m : ℕ, m = (2 + Real.sqrt 5) ^ n + (2 - Real.sqrt 5) ^ n := by
  -- Perform induction on N.
  induction' N with N hN
  . -- Show the base case N = 0.
    intro n hn
    simp at hn
    use 2
    norm_num [hn]
  . -- Show the inductive case.
    intro n hn'
    by_cases hn : n ≤ N
    . -- For n ≤ N, use the inductive hypothesis directly.
      exact hN n hn
    . -- Otherwise, we use the previous lemmas and the inductive hypothesis to prove that the term is a natural number for N as well.
      replace hn : n = N + 1 := by
        omega
      -- We deal with N = 0 specially.
      by_cases hN' : N = 0
      . simp [hn, hN']
        use 4
        norm_num
      . rw [hn]
        obtain ⟨m₀, hN₀⟩ := hN (N - 1) (by omega)
        obtain ⟨m₁, hN₁⟩ := hN N (by rfl)
        use 4 * m₁ + m₀
        rw [show N + 1 = N - 1 + 2 by omega, iter_term_p (N - 1), iter_term_m (N - 1), show N - 1 + 1 = N by omega]
        push_cast
        rw [hN₀, hN₁]
        ring

-- Lemma which shows that ⌊(2 + √5) ^ (2n + 1)⌋ = (2 + √5) ^ (2n + 1) + (2 - √5) ^ (2n + 1) for any natural number n.
lemma sum_eq_floor (n : ℕ) : Nat.floor ((2 + Real.sqrt 5) ^ (2 * n + 1)) = (2 + Real.sqrt 5) ^ (2 * n + 1) + (2 - Real.sqrt 5) ^ (2 * n + 1) := by
  -- Note that the right hand side is an integer.
  obtain ⟨m, h₀⟩ := sum_is_nat (2 * n + 1) (2 * n + 1) (by rfl)
  -- Use the definition of floor function.
  rw [<-h₀]
  norm_cast
  rw [Nat.floor_eq_iff (by positivity)]
  have g₀ : 0 ≤ Real.sqrt 5 - 2 := by
    simp
    rw [Real.le_sqrt]
    <;> norm_num
  refine ⟨?_, ?_,⟩
  . -- Show that (2 + √5) ^ (2 * n + 1) + (2 - √5) ^ (2 * n + 1) ≤ (2 + √5) ^ (2 * n + 1).
    simp [h₀]
    rw [show 2 - Real.sqrt 5 = -(Real.sqrt 5 - 2) by ring, Odd.neg_pow (by use n)]
    simp
    positivity
  . -- Show that (2 + √5) ^ (2 * n + 1) < 2 + √5) ^ (2 * n + 1) + (2 - √5) ^ (2 * n + 1) + 1.
    rw [h₀, add_assoc]
    simp
    rw [show 2 - Real.sqrt 5 = -(Real.sqrt 5 - 2) by ring, Odd.neg_pow (by use n)]
    simp
    have g₁ : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt]
      <;> norm_num
    calc
      _ ≤ Real.sqrt 5 - 2 := by
        apply pow_le_of_le_one
        <;> linarith
      _ < 1 := by
        linarith
  
-- Lemma which shows that 4 ∣ (2 + √5) ^ (2n + 1) for any natural number n.
lemma four_dvd_lemma (n : ℕ) : 4 ∣ Nat.floor ((2 + Real.sqrt 5) ^ (2 * n + 1)) := by
  -- Perform induction on n.
  induction' n with n hn
  . -- Show the base case n = 0.
    -- We have 4 = ⌊2 + √5⌋ divisible by 4.
    suffices Nat.floor (2 + Real.sqrt 5) = 4 by
      simp [this]
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    refine ⟨by linarith [bound_sqrt_5], by linarith [bound_sqrt_5]⟩
  . -- Show the inductive case.
    suffices Nat.floor ((2 + Real.sqrt 5) ^ (2 * (n + 1) + 1)) = Nat.floor ((2 + Real.sqrt 5) ^ (2 * n + 1)) + 4 * ((2 + Real.sqrt 5) ^ (2 * (n + 1)) + (2 - Real.sqrt 5) ^ (2 * (n + 1))) by
      -- We use the inductive hypothesis and the recurrence relation we found as in the lemma.
      obtain ⟨m, hn'⟩ := sum_is_nat (2 * (n + 1)) (2 * (n + 1)) (by rfl)
      rw [<-hn'] at this
      norm_cast at this
      rw [this, <-Nat.dvd_add_iff_right hn]
      simp
    iterate 2 rw [sum_eq_floor]
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, iter_term_p, iter_term_m]
    ring

/- Prove that the number $\lfloor (2+\sqrt5)^{2019} \rfloor$ is not prime.
 -/
theorem number_theory_86265 : ¬Nat.Prime (Nat.floor ((2 + Real.sqrt 5) ^ 2019)) := by
  -- We prove by contradiction and note that 4 ∣ ⌊(2 + √5) ^ 2019⌋.
  by_contra! h₀
  have h₁ : 2 * 2 ∣ Nat.floor ((2 + Real.sqrt 5) ^ 2019) := by
    -- We use the lemmas shown above.
    have := four_dvd_lemma 1009
    simp_all
  have h₂ := h₁
  apply dvd_of_mul_left_dvd at h₁
  rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two h₀] at h₁
  norm_num [<-h₁] at h₂

