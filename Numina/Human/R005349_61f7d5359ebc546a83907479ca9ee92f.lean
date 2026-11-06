import Mathlib

/- Suppose $p$ is a prime greater than 3 . Find all pairs of integers $(a, b)$ satisfying the equation

$$
a^{2}+3 a b+2 p(a+b)+p^{2}=0
$$ -/
theorem algebra_607810 (p : ℕ) (hp : Nat.Prime p) (h : p > 3) :
    {(a, b) : ℤ × ℤ | a ^ 2 + 3 * a * b + 2 * p * (a + b) + p ^ 2 = 0}
    = if p % 3 = 1 then {((-2 * (p / 3 : ℕ) - 1 : ℤ), ((p / 3 : ℕ) ^ 2 : ℤ)), ((-p : ℤ), (0 : ℤ)), ((-p * ((p / 3 : ℕ) + 1) : ℤ), ((p / 3 : ℕ) ^ 2 : ℤ))} else {((-2 * (p / 3 : ℕ) - 1 : ℤ), (-((p / 3 : ℕ) + 1) ^ 2 : ℤ)), ((-p : ℤ), (0 : ℤ)), ((p * (p / 3 : ℕ) : ℤ), (-((p / 3 : ℕ) + 1) ^ 2 : ℤ))} := by
  -- Note that p % 3 is either 1 or 2.
  have h₃ : p % 3 = 1 ∨ p % 3 = 2 := by
    -- We have 3 ∤ p.
    have h₃ : ¬3 ∣ p := by
      by_contra! h₃
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hp] at h₃
      norm_num [<-h₃] at h
    omega
  ext ⟨a, b⟩
  simp only [Set.mem_setOf]
  apply Iff.intro
  . -- Show that the equation implies such solutions.
    intro h₀
    -- Show that 3a + 2p ∣ (a + p)².
    have h₁ : 3 * a + 2 * p ∣ (a + p) ^ 2 := by
      rw [dvd_iff_exists_eq_mul_left]
      use -b
      linarith
    -- Show that 3a + 2p ∣ p².
    have h₂ : 3 * a + 2 * p ∣ p ^ 2 := by
      rw [<-@dvd_add_right _ _ _ ((3 * a + 2 * p) ^ 2 + 2 * (3 * a + 2 * p) * p), <-add_sq, show (3 * a + 2 * p + p) ^ 2 = 9 * (a + p) ^ 2 by ring]
      . -- Show that 3a + 2p ∣ 9(a + p)².
        calc
          _ ∣ (a + p) ^ 2 := h₁
          _ ∣ 9 * (a + p) ^ 2 := by
            apply dvd_mul_left
      .  -- Show that 3a + 2p ∣ (3a + 2p)² + 2(3a + 2p)p.
        rw [show (3 * a + 2 * p) ^ 2 + 2 * (3 * a + 2 * p) * p = (3 * a + 2 * p) * (3 * a + 4 * p) by ring]
        apply dvd_mul_right
    -- Consider the divisors of p², which are only ±1, ±p and ±p².
    replace h₂ : (3 * a + 2 * p).natAbs ∈ (p ^ 2).divisors := by
      rw [Nat.mem_divisors]
      zify
      rw [abs_dvd]
      simp [h₂, show p ≠ 0 by linarith]
    rw [Nat.Prime.divisors_sq hp] at h₂
    simp at h₂
    iterate 3 rw [Int.natAbs_eq_iff] at h₂
    rcases h₃ with (h₃ | h₃)
    . -- Suppose p % 3 = 1, let p = 3k + 1.
      have h₄ := Nat.mod_add_div p 3
      rw [h₃] at h₄
      set k := p / 3 with h₅
      simp [h₃]
      rcases h₂ with ((h₂ | h₂) | (h₂ | h₂) | (h₂ | h₂))
      . -- Suppose 3a + 2p = p², which is impossible.
        -- We get 3 ∣ p(p - 2).
        replace h₂ : 3 * a = p * (p - 2 : ℤ) := by
          zify at h₂ ⊢
          linarith
        replace h₂ : 3 ∣ p * (p - 2) := by
          zify
          rw [Int.ofNat_sub (by omega)]
          simp 
          rw [<-h₂]
          apply dvd_mul_right
        -- We have 3 ∣ p or 3 ∣ p - 2, which is absurd.
        rw [Nat.Prime.dvd_mul Nat.prime_three] at h₂
        omega
      . -- Suppose 3a + 2p = -p².
        right
        right
        have : a = -(p * (k + 1)) := by
          rw [<-h₄] at h₂ ⊢
          push_cast at h₂ ⊢
          linarith
        refine ⟨this, ?_⟩
        replace h₀ : (-p ^ 2) * b + (a + p) ^ 2 = 0 := by
          push_cast at h₂
          rw [<-h₂]
          linarith
        rw [this] at h₀
        ring_nf at h₀
        replace h₀ : (k ^ 2 - b) * p ^ 2 = 0 := by
          linarith
        simp [show p ≠ 0 by linarith] at h₀
        linarith
      . -- Suppose 3a + 2p = p, which is impossible.
        rw [<-h₄] at h₂
        -- We get 3 ∣ -1, which is a contradiction.
        replace h₂ : 3 * (a + k) = -1 := by
          zify at h₂ ⊢
          linarith
        replace h₂ : 3 ∣ -1 := by
          rw [<-h₂]
          apply dvd_mul_right
        norm_num at h₂
      . -- Suppose 3a + 2p = -p.
        right
        left
        have : a = -p := by
          linarith
        refine ⟨this, ?_⟩
        rw [this, <-h₄] at h₀
        replace h₀ : p * b = 0 := by
          rw [<-h₄]
          push_cast at h₀ ⊢
          linarith
        simp [show p ≠ 0 by linarith] at h₀
        exact h₀
      . -- Suppose 3a + 2p = 1, which is impossible.
        rw [<-h₄] at h₂
        -- We get 3 ∣ -1, which is a contradiction.
        replace h₂ : 3 * (2 * k + a) = -1 := by
          zify at h₂ ⊢
          linarith
        replace h₂ : 3 ∣ -1 := by
          rw [<-h₂]
          apply dvd_mul_right
        norm_num at h₂
      . -- Suppose 3a + 2p = -1.
        left
        rw [<-h₄] at h₂
        push_cast at h₂
        -- We have a = -2k - 1 and b = k².
        have : a = -2 * k - 1 := by
          linarith
        refine ⟨this, ?_⟩
        rw [this, <-h₄] at h₀
        push_cast at h₀
        linarith
    . -- Suppose p % 3 = 2, and let p = 3k + 2.
      have h₄ := Nat.mod_add_div p 3
      rw [h₃] at h₄
      set k := p / 3 with h₅
      simp [h₃]
      rcases h₂ with ((h₂ | h₂) | (h₂ | h₂) | (h₂ | h₂))
      . -- Suppose 3a + 2p = p².
        right
        right
        have : a = p * k := by
          rw [<-h₄] at h₂ ⊢
          push_cast at h₂ ⊢
          linarith
        refine ⟨this, ?_⟩
        replace h₀ : (p ^ 2) * b + (a + p) ^ 2 = 0 := by
          push_cast at h₂
          rw [<-h₂]
          linarith
        replace h₀ : ((k + 1 : ℕ) ^ 2 + b) * p ^ 2 = 0 := by
          rw [this, <-mul_add_one, mul_pow] at h₀
          push_cast
          linarith
        simp [show p ≠ 0 by linarith] at h₀
        linarith
      . -- Suppose 3a + 2p = -p², which is impossible.
        -- We get 3 ∣ p(p + 2).
        replace h₂ : 3 * -a = p * (p + 2 : ℤ) := by
          zify at h₂ ⊢
          linarith
        replace h₂ : 3 ∣ p * (p + 2) := by
          zify
          rw [<-h₂]
          apply dvd_mul_right
        -- We have 3 ∣ p or 3 ∣ p + 2, which is absurd.
        rw [Nat.Prime.dvd_mul Nat.prime_three] at h₂
        omega
      . -- Suppose 3a + 2p = p, which is impossible.
        rw [<-h₄] at h₂
        -- We get 3 ∣ -2, which is a contradiction.
        replace h₂ : 3 * (a + k) = -2 := by
          zify at h₂ ⊢
          linarith
        replace h₂ : 3 ∣ -2 := by
          rw [<-h₂]
          apply dvd_mul_right
        norm_num at h₂
      . -- Suppose 3a + 2p = -p.
        right
        left
        have : a = -p := by
          linarith
        refine ⟨this, ?_⟩
        rw [this, <-h₄] at h₀
        replace h₀ : p * b = 0 := by
          rw [<-h₄]
          push_cast at h₀ ⊢
          linarith
        simp [show p ≠ 0 by linarith] at h₀
        exact h₀
      . -- Suppose 3a + 2p = 1.
        left
        rw [<-h₄] at h₂
        push_cast at h₂
        -- We have a = -2k - 1 and b = -(k + 1) ^ 2.
        have : a = -2 * k - 1 := by
          linarith
        refine ⟨this, ?_⟩
        rw [this, <-h₄] at h₀
        push_cast at h₀
        linarith
      . -- Suppose 3a + 2p = -1, which is impossible.
        rw [<-h₄] at h₂
        -- We get 3 ∣ -5, which is a contradiction.
        replace h₂ : 3 * (2 * k + a) = -5 := by
          zify at h₂ ⊢
          linarith
        replace h₂ : 3 ∣ -5 := by
          rw [<-h₂]
          apply dvd_mul_right
        norm_num at h₂
  . -- Show that such solutions indeed satisfy the equation.
    rcases h₃ with (h₃ | h₃)
    . -- Suppose p % 3 = 1, let p = 3k + 1.
      have h₂ := Nat.mod_add_div p 3
      set k := p / 3 with h₄
      simp [h₃]
      rw [h₃] at h₂
      intro h₀
      -- Substitute the values of a and b.
      rcases h₀ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      . rw [<-h₂]
        push_cast
        ring
      . ring
      . rw [<-h₂]
        push_cast
        ring
    . -- Suppose p % 3 = 2, let p = 3k + 2.
      have h₂ := Nat.mod_add_div p 3
      set k := p / 3 with h₄
      simp [h₃]
      rw [h₃] at h₂
      intro h₀
      -- Substitute the values of a and b.
      rcases h₀ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      . rw [<-h₂]
        push_cast
        ring
      . ring
      . rw [<-h₂]
        push_cast
        ring
