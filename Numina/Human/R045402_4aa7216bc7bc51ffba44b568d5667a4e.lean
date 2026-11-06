import Mathlib

set_option maxHeartbeats 999999999999999

/--
Task 1. The sequence of positive integers $a_{0}, a_{1}, a_{2}, \ldots$ is defined by $a_{0}=3$ and

$$
a_{n+1}-a_{n}=n\left(a_{n}-1\right)
$$

for all $n \geq 0$. Determine all integers $m \geq 2$ for which $\operatorname{gcd}\left(m, a_{n}\right)=1$ for all $n \geq 0$.
-/

theorem number_theory_169458 (a : ℕ → ℕ) (ha0 : a 0 = 3)
    (han : ∀ n, a (n + 1) = n * (a n - 1) + a n) :
    {m | 2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1} = {m | ∃ k, m = 2 ^ (k + 1)} := by
  have h_closed_form : ∀ n, a n = 2 * Nat.factorial n + 1 := by
    intro n
    induction n with
    | zero =>
      calc _ = a 0 := by rfl
        _ = 3 := by exact ha0
        _ = 2 * Nat.factorial 0 + 1 := by simp
    | succ n ih =>
      calc _ = a (n + 1) := by rfl
        _ = n * (a n - 1) + a n := by exact han n
        _ = n * (2 * Nat.factorial n + 1 - 1) + (2 * Nat.factorial n + 1) := by
          rw [show a n = 2 * Nat.factorial n + 1 by exact ih]
        _ = n * (2 * Nat.factorial n) + (2 * Nat.factorial n + 1) := by
          simp [Nat.mul_sub, Nat.add_comm]
          <;> ring
        _ = 2 * Nat.factorial (n + 1) + 1 := by
          rw [Nat.factorial_succ]
          ring

  have hwilson := @Nat.prime_iff_fac_equiv_neg_one
  
  have h_main_imp : ∀ m, (2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1) → (∃ k, m = 2 ^ (k + 1)) := by
    intro m hm
    have h₁ : 2 ≤ m := hm.1
    have h₂ : ∀ n, Nat.gcd m (a n) = 1 := hm.2
    by_contra! h₃
    -- find an odd prime
    have h₄ : ∃ p, p.Prime ∧ p ∣ m ∧ p ≠ 2 := by
      by_contra jj
      push_neg at jj
      -- all prime factors of m are 2's and thus contradicts
      have fz : ∃ k, m = 2^(k + 1) := by
        clear * - jj h₁
        -- we enumerate all prime factors
        induction' m using induction_on_primes with p aa hp ih
        · norm_num at h₁
        · norm_num at h₁
        · cases' aa with aa
          · norm_num at h₁
          cases' aa with aa
          · simp only [zero_add, Nat.not_ofNat_le_one, Nat.dvd_one, IsEmpty.forall_iff,
            mul_one] at *
            exists 0
            norm_num
            apply jj <;> simpa
          have ihh := ih (by norm_num) (by {
            intros pp hhp hdv
            apply jj
            · assumption
            · clear * - hdv; exact Dvd.dvd.mul_left hdv p
          })
          obtain ⟨k, kk⟩ := ihh
          exists k + 1
          rw [kk]
          rw [jj p hp (by clear * -; exact Nat.dvd_mul_right p (aa + 1 + 1))]
          ring
      clear jj
      obtain ⟨ll, kk⟩ := fz
      exact h₃ _ kk
    -- now we have that odd prime yippee
    obtain ⟨p, hp, dvd, neq_two⟩ := h₄
    have ma := h_closed_form (p - 3)
    have al := (@hwilson p (by clear * - hp; exact Nat.Prime.ne_one hp)).mp hp
    have msl : p ∣ a (p - 3) := by
      rw [h_closed_form]
      clear * - p hp dvd neq_two al
      revert m p hp dvd neq_two al
      intro m p hp hpm hp_ne_2 h_wilson
      have h₁ : p ≥ 3 := by
        have h₁ := Nat.Prime.two_le hp
        have h₂ : p ≠ 2 := hp_ne_2
        have h₃ : p ≥ 3 := by
          by_contra h
          have h₄ : p ≤ 2 := by omega
          interval_cases p <;> contradiction
        exact h₃
        <;> omega
      
      have h₂ : (p - 1 : ℕ) ≥ 2 := by
        have h₂ : p ≥ 3 := h₁
        have h₃ : p - 1 ≥ 2 := by
          have h₄ : p ≥ 3 := h₂
          omega
        exact_mod_cast h₃
      
      have h₃ : (p - 1 : ℕ) = p - 1 := by rfl
      
      have h₄ : (p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial = (p - 1).factorial := by
        have h₄ : p ≥ 3 := h₁
        have h₅ : (p - 1 : ℕ) ≥ 2 := h₂
        have h₆ : (p - 1 : ℕ) = p - 1 := h₃
        have h₇ : (p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial = (p - 1).factorial := by
          have h₈ : (p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial = (p - 1).factorial := by
            have h₉ : ∀ (n : ℕ), n ≥ 3 → (n - 1 : ℕ) * (n - 2 : ℕ) * (n - 3).factorial = (n - 1).factorial := by
              intro n hn
              have h₁₀ : n ≥ 3 := hn
              have h₁₁ : (n - 1 : ℕ) ≥ 2 := by omega
              have h₁₂ : (n - 2 : ℕ) ≥ 1 := by omega
              have h₁₃ : (n - 3 : ℕ) ≤ (n - 1 : ℕ) := by omega
              have h₁₄ : (n - 1 : ℕ) * (n - 2 : ℕ) * (n - 3).factorial = (n - 1).factorial := by
                have h₁₅ : (n - 1 : ℕ) * (n - 2 : ℕ) * (n - 3).factorial = (n - 1).factorial := by
                  induction' n with k hk
                  · norm_num at *
                  · cases k with
                    | zero => contradiction
                    | succ k =>
                      cases k with
                      | zero => contradiction
                      | succ k =>
                        simp_all [Nat.factorial_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
                          <;> ring_nf at *
                          <;> nlinarith
                exact h₁₅
              exact h₁₄
            exact h₉ p h₄
          exact h₈
        exact h₇
      
      have h₅ : (↑((p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial) : ZMod p) = (-1 : ZMod p) := by
        have h₅ : (↑((p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial) : ZMod p) = (↑((p - 1).factorial) : ZMod p) := by
          rw [h₄]
        rw [h₅]
        rw [h_wilson]
        <;> simp [ZMod.cast_neg, ZMod.cast_one]
        <;> simp_all [ZMod.cast_id, Nat.cast_add, Nat.cast_mul, Nat.cast_sub, Nat.cast_one]
        <;> simp_all [ZMod.cast_id, Nat.cast_add, Nat.cast_mul, Nat.cast_sub, Nat.cast_one]
        <;> omega
      
      have h₆ : (↑((p - 1 : ℕ) : ZMod p) : ZMod p) = (-1 : ZMod p) := by
        haveI : Fact p.Prime := ⟨hp⟩
        have h₆ : (p : ℕ) ≥ 3 := h₁
        have h₇ : (p : ℕ) > 0 := Nat.Prime.pos hp
        have h₈ : (p : ℕ) ≠ 0 := by clear * - h₇; omega
        have h₉ : (↑((p - 1 : ℕ) : ZMod p) : ZMod p) = (-1 : ZMod p) := by
          have h₁₀ : (p - 1 : ℕ) < p := by omega
          have h₁₁ : ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
            -- Use the fact that p - 1 ≡ -1 mod p
            rw [(by norm_num : (-1 : ZMod p) = (-1 : ℤ))]
            rw [(by norm_num : (↑(p - 1) : ZMod p) = (↑(p - 1) : ℤ))]
            rw [ZMod.intCast_eq_intCast_iff]
            push_cast [(by clear * - h₆; omega : p ≥ 1)]
            clear * - h₆
            have h₇ : ((p : ℤ) - 1) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
              have h₈ : ((p : ℤ) - 1 : ℤ) = (p : ℤ) + (-1 : ℤ) := by ring
              rw [h₈]
              have h₉ : ((p : ℤ) + (-1 : ℤ)) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
                simp [Int.add_emod, Int.emod_emod]
              exact h₉
            
            rw [Int.ModEq]
            exact h₇
          simpa [h₁₁] using h₁₁
        exact h₉
        <;> simp_all [ZMod.cast_add, ZMod.cast_mul, ZMod.cast_one, ZMod.cast_sub, ZMod.cast_pow]
        <;> norm_num
        <;> omega
      
      have h₇ : (↑((p - 2 : ℕ) : ZMod p) : ZMod p) = (-2 : ZMod p) := by
        haveI : Fact p.Prime := ⟨hp⟩
        have h₇ : (p : ℕ) ≥ 3 := h₁
        have h₈ : (p : ℕ) > 0 := Nat.Prime.pos hp
        have h₉ : (p : ℕ) ≠ 0 := by clear * - h₈; omega
        have h₁₀ : (p - 2 : ℕ) < p := by omega
        have h₁₁ : ((p - 2 : ℕ) : ZMod p) = (-2 : ZMod p) := by
          -- Use the fact that p - 2 ≡ -2 mod p
            rw [(by norm_num : (-2 : ZMod p) = (-2 : ℤ))]
            rw [(by norm_num : (↑(p - 2) : ZMod p) = (↑(p - 2) : ℤ))]
            rw [ZMod.intCast_eq_intCast_iff]
            push_cast [(by clear * - h₇; omega : p ≥ 2)]
            clear * - h₇
            have h99 : ((p : ℤ) - 2) % (p : ℤ) = (-2 : ℤ) % (p : ℤ) := by
              have h₈ : ((p : ℤ) - 2 : ℤ) = (p : ℤ) + (-2 : ℤ) := by ring
              rw [h₈]
              have h₉ : ((p : ℤ) + (-2 : ℤ)) % (p : ℤ) = (-2 : ℤ) % (p : ℤ) := by
                simp [Int.add_emod, Int.emod_emod]
              exact h₉
            
            rw [Int.ModEq]
            exact h99
          <;> simp [h₁₀, Nat.cast_sub, Nat.cast_one, Nat.mod_eq_of_lt]
          <;> omega
        simpa [h₁₁] using h₁₁
        <;> simp_all [ZMod.cast_add, ZMod.cast_mul, ZMod.cast_one, ZMod.cast_sub, ZMod.cast_pow]
        <;> norm_num
        <;> omega
      
      have h₈ : (↑(2 * (p - 3).factorial + 1 : ℕ) : ZMod p) = 0 := by
        have h₈₁ : (↑((p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial) : ZMod p) = (-1 : ZMod p) := h₅
        have h₈₂ : (↑((p - 1 : ℕ) : ZMod p) : ZMod p) = (-1 : ZMod p) := h₆
        have h₈₃ : (↑((p - 2 : ℕ) : ZMod p) : ZMod p) = (-2 : ZMod p) := h₇
        have h₈₄ : (↑((p - 1 : ℕ) * (p - 2 : ℕ) * (p - 3).factorial) : ZMod p) = (↑((p - 1 : ℕ) : ZMod p) * ↑((p - 2 : ℕ) : ZMod p) * ↑((p - 3).factorial : ℕ)) := by
          simp [mul_assoc, Nat.cast_mul]
          <;> ring_nf
          <;> simp_all [ZMod.nat_cast_self]
          <;> norm_num
          <;> simp_all [ZMod.nat_cast_self]
          <;> norm_num
        rw [h₈₄] at h₈₁
        rw [h₈₂, h₈₃] at h₈₁
        have h₈₅ : ((-1 : ZMod p) * (-2 : ZMod p) * (↑((p - 3).factorial : ℕ) : ZMod p)) = (-1 : ZMod p) := by
          simpa [mul_assoc] using h₈₁
        have h₈₆ : ((-1 : ZMod p) * (-2 : ZMod p) * (↑((p - 3).factorial : ℕ) : ZMod p)) = (2 * (↑((p - 3).factorial : ℕ)) : ZMod p) := by
          ring_nf at h₈₁ ⊢
          <;> simp_all [ZMod.nat_cast_self]
          <;> norm_num
          <;> simp_all [ZMod.nat_cast_self]
          <;> norm_num
          <;> ring_nf at *
          <;> simp_all [ZMod.nat_cast_self]
          <;> norm_num
          <;> omega
        rw [h₈₆] at h₈₅
        have h₈₇ : (2 * (↑((p - 3).factorial : ℕ) : ZMod p)) = (-1 : ZMod p) := by
          simpa [mul_assoc] using h₈₅
        have h₈₈ : (↑(2 * (p - 3).factorial + 1 : ℕ) : ZMod p) = 0 := by
          have h₈₉ : (↑(2 * (p - 3).factorial + 1 : ℕ) : ZMod p) = (2 * (↑((p - 3).factorial : ℕ) : ZMod p) + 1) := by
            simp [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
            <;> ring_nf
            <;> simp_all [ZMod.nat_cast_self]
            <;> norm_num
          rw [h₈₉]
          have h₈₁₀ : (2 * (↑((p - 3).factorial : ℕ) : ZMod p) + 1 : ZMod p) = 0 := by
            have h₈₁₁ : (2 * (↑((p - 3).factorial : ℕ) : ZMod p) : ZMod p) = (-1 : ZMod p) := by
              simpa [mul_assoc] using h₈₇
            rw [h₈₁₁]
            simp [add_eq_zero_iff_eq_neg]
            <;> ring_nf at *
            <;> simp_all [ZMod.nat_cast_self]
            <;> norm_num
            <;> omega
          rw [h₈₁₀]
        exact h₈₈
      
      have h₉ : p ∣ 2 * (p - 3).factorial + 1 := by
        have h₉₀ : (↑(2 * (p - 3).factorial + 1 : ℕ) : ZMod p) = 0 := h₈
        have h₉₁ : p ∣ 2 * (p - 3).factorial + 1 := by
          -- Use the fact that if a number is zero in ZMod p, then p divides that number.
          rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd]
          simpa using h₉₀
        exact h₉₁
      
      exact h₉
    -- now p divides a (p - 3)
    -- we set up a contradiction
    have ls := h₂ (p - 3)
    revert hp msl ls dvd
    clear * -
    revert a m p
    intro a m p hp h_dvd_m h_dvd_a h_gcd
    have h_p_dvd_gcd : p ∣ m.gcd (a (p - 3)) := by
      apply Nat.dvd_gcd h_dvd_m h_dvd_a
    
    have h_p_dvd_one : p ∣ 1 := by
      rw [h_gcd] at h_p_dvd_gcd
      exact h_p_dvd_gcd
    
    have h_false : False := by
      have h₁ : ¬p ∣ 1 := Nat.Prime.not_dvd_one hp
      exact h₁ h_p_dvd_one
    
    exact h_false

  have h_main_converse : ∀ m, (∃ k, m = 2 ^ (k + 1)) → (2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1) := by
    intro m hm
    have h₁ : 2 ≤ m := by
      obtain ⟨k, hk⟩ := hm
      rw [hk]
      have h₂ : 0 < 2 ^ (k + 1) := by positivity
      have h₃ : 2 ≤ 2 ^ (k + 1) := by
        have h₄ : 1 ≤ 2 ^ (k + 1) := by
          have h₅ : 0 < 2 ^ (k + 1) := by positivity
          linarith
        have h₅ : 2 ≤ 2 ^ (k + 1) := by
          have h₆ : 2 ^ (k + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
          linarith
        linarith
      linarith
    have h₂ : ∀ n, Nat.gcd m (a n) = 1 := by
      intro n
      obtain ⟨k, hk⟩ := hm
      rw [hk]
      have h₃ : ∀ n, Nat.gcd (2 ^ (k + 1)) (a n) = 1 := by
        intro n
        have h₄ : a n = 2 * Nat.factorial n + 1 := h_closed_form n
        rw [h₄]
        have h₅ : Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
          have h₆ : 2 * Nat.factorial n + 1 > 0 := by positivity
          have h₇ : 2 * Nat.factorial n % 2 = 0 := by
            have h₈ : Nat.factorial n > 0 := Nat.factorial_pos n
            have h₉ : 2 * Nat.factorial n % 2 = 0 := by
              omega
            exact h₉
          have h₈ : (2 * Nat.factorial n + 1) % 2 = 1 := by
            omega
          have h₉ : Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
            have h₁₀ : Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
              have h₁₁ : ∀ k n : ℕ, Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
                intro k n
                have h₁₂ : 2 * Nat.factorial n + 1 > 0 := by positivity
                have h₁₃ : 2 * Nat.factorial n % 2 = 0 := by
                  have h₁₄ : Nat.factorial n > 0 := Nat.factorial_pos n
                  have h₁₅ : 2 * Nat.factorial n % 2 = 0 := by
                    omega
                  exact h₁₅
                have h₁₆ : (2 * Nat.factorial n + 1) % 2 = 1 := by
                  omega
                have h₁₇ : Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
                  have h₁₈ : ∀ k n : ℕ, Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
                    intro k n
                    have h₁₉ : 2 * Nat.factorial n + 1 > 0 := by positivity
                    have h₂₀ : 2 * Nat.factorial n % 2 = 0 := by
                      have h₂₁ : Nat.factorial n > 0 := Nat.factorial_pos n
                      have h₂₂ : 2 * Nat.factorial n % 2 = 0 := by
                        omega
                      exact h₂₂
                    have h₂₃ : (2 * Nat.factorial n + 1) % 2 = 1 := by
                      omega
                    have h₂₄ : Nat.gcd (2 ^ (k + 1)) (2 * Nat.factorial n + 1) = 1 := by
                      apply Nat.Coprime.pow_left
                      <;> norm_num
                      <;>
                      (try omega)
                      <;>
                      (try
                        simp_all [Nat.factorial_succ, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
                      <;> norm_num)
                      <;>
                      (try
                        omega)
                    exact h₂₄
                  exact h₁₈ k n
                exact h₁₇
              exact h₁₁ k n
            exact h₁₀
          exact h₉
        exact h₅
      exact h₃ n
    exact ⟨h₁, h₂⟩
  
  have h_final : {m | 2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1} = {m | ∃ k, m = 2 ^ (k + 1)} := by
    apply Set.ext
    intro m
    constructor
    · intro hm
      have h₁ : ∃ k, m = 2 ^ (k + 1) := by
        have h₂ : 2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1 := hm
        have h₃ : ∃ k, m = 2 ^ (k + 1) := by
          apply h_main_imp
          exact h₂
        exact h₃
      exact h₁
    · intro hm
      have h₁ : 2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1 := by
        have h₂ : ∃ k, m = 2 ^ (k + 1) := hm
        have h₃ : 2 ≤ m ∧ ∀ n, Nat.gcd m (a n) = 1 := by
          apply h_main_converse
          exact h₂
        exact h₃
      exact h₁
  -- The final step is to use the previously proven statements to conclude the theorem.
  simpa using h_final
