import Mathlib

/- Find all prime numbers $p$ and nonnegative integers $x \neq y$ such that $x^{4}-y^{4}=$ $p\left(x^{3}-y^{3}\right)$.-/
theorem number_theory_606153 :
    {(x, y, p) : ℕ × ℕ × ℕ | Nat.Prime p ∧ x ≠ y ∧ (x ^ 4 - y ^ 4 : ℤ) = p * (x ^ 3 - y ^ 3)} = {(p, 0, p) | (p : ℕ) (_ : Nat.Prime p)} ∪ {(0, p, p) | (p : ℕ) (_ : Nat.Prime p)} := by
  -- Simplify the goal into two parts.
  ext ⟨x, y, p⟩
  simp
  apply Iff.intro
  . -- First show that the condition implies that (x, y) = (0, p) or (p, 0).
    rintro ⟨hp, hxy, h₀⟩
    -- Let d = gcd (x, y).
    let d := Nat.gcd x y
    -- We have x = da and y = db for some coprime a, b.
    have ha : d ∣ x := by
      simp [d]
      apply Nat.gcd_dvd_left
    have hb : d ∣ y := by
      simp [d]
      apply Nat.gcd_dvd_right
    rw [dvd_iff_exists_eq_mul_right] at ha hb
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    -- We have d > 0, otherwise x = y = 0, contradicing our assumption that x ≠ y.
    have hd : d ≠ 0 := by
      simp [d]
      rw [Nat.gcd_eq_zero_iff]
      by_contra!
      simp [this] at hxy
    -- Show that a and b are coprime.
    have hab : Nat.gcd a b = 1 := by
      suffices Nat.gcd (d * a) (d * b) = d by
        rw [Nat.gcd_mul_left, Nat.mul_eq_left hd] at this
        exact this
      rw [<-ha, <-hb]
    -- We have d(a + b)(a² + b²) = p(a² + ab + b²) by first multiplying d³ on the left and (a - b) at the right on both sides, then cancel them.
    have h₁ : d ^ 3 * d * (a + b) * (a ^ 2 + b ^ 2) * (a - b : ℤ) = d ^ 3 * p * (a ^ 2 + a * b + b ^ 2) * (a - b) := by
      ring_nf
      repeat rw [<-mul_pow]
      zify at ha hb
      rw [<-ha, <-hb, <-sub_mul, h₀]
      ac_rfl
    rw [Int.mul_eq_mul_right_iff (by by_contra!; apply eq_of_sub_eq_zero at this; simp_all), mul_assoc, mul_assoc, mul_assoc, Int.mul_eq_mul_left_iff (by simp [hd])] at h₁
    norm_cast at h₁
    -- We have a + b and a² + ab + b² coprime.
    have hab' : Nat.Coprime (a + b) (a ^ 2 + a * b + b ^ 2) := by
      apply Nat.coprime_of_dvd'
      -- It suffices to show that no prime divides both of them.
      intro q hq g₀ g₁
      -- Since q ∣ a + b and q ∣ a ^ 2 + ab + b ^ 2, we have q ∣ ab.
      have g₂ : (q : ℤ) ∣ ((a + b) ^ 2 - (a ^ 2 + a * b + b ^ 2) : ℤ) := by
        replace g₀ := dvd_pow g₀ (show 2 ≠ 0 by norm_num)
        zify at g₀ g₁
        apply dvd_sub g₀ g₁
      ring_nf at g₂
      norm_cast at g₂
      -- We have q ∣ ab, but also q ∣ a + b, so q ∣ a and q ∣ b.
      have g₃ : q ∣ a ∧ q ∣ b := by
        have := (Nat.Prime.dvd_mul hq).mp g₂
        cases this with
        | inl this =>
          rw [<-Nat.dvd_add_iff_right this] at g₀
          tauto
        | inr this =>
          rw [<-Nat.dvd_add_iff_left this] at g₀
          tauto
      -- Since q ∣ a and q ∣ b, we have q ∣ Nat.gcd a b.
      rw [<-hab]
      exact Nat.dvd_gcd_iff.mpr g₃
    -- We have a² + b² and a² + ab + b₆2 coprime.
    have hab'' : Nat.Coprime (a ^ 2 + b ^ 2) (a ^ 2 + a * b + b ^ 2) := by
      apply Nat.coprime_of_dvd'
      -- It suffices to show that no prime divides both of them.
      intro q hq g₀ g₁
      -- Since q ∣ a + b and q ∣ a ^ 2 + ab + b ^ 2, we have q ∣ ab.
      have g₂ : (q : ℤ) ∣ ((a ^ 2 + a * b + b ^ 2) - (a ^ 2 + b ^ 2): ℤ) := by
        zify at g₀ g₁
        apply dvd_sub g₁ g₀
      ring_nf at g₂
      norm_cast at g₂
      replace g₂ := dvd_pow g₂ (show 2 ≠ 0 by norm_num)
      rw [mul_pow] at g₂
      -- We have q ∣ a²b², but also q ∣ a² + b², so q ∣ a and q ∣ b.
      have g₃ : q ∣ a ^ 2 ∧ q ∣ b ^ 2 := by
        have := (Nat.Prime.dvd_mul hq).mp g₂
        cases this with
        | inl this =>
          rw [<-Nat.dvd_add_iff_right this] at g₀
          tauto
        | inr this =>
          rw [<-Nat.dvd_add_iff_left this] at g₀
          tauto
      iterate 2 rw [Prime.dvd_pow_iff_dvd (Nat.prime_iff.mp hq) (by norm_num)] at g₃
      -- Since q ∣ a and q ∣ b, we have q ∣ Nat.gcd a b.
      rw [<-hab]
      exact Nat.dvd_gcd_iff.mpr g₃
    -- Show that (a + b)(a² + b²) ∣ p (a ^ 2 + a * b + b ^ 2).
    replace h₁ : ((a + b) * (a ^ 2 + b ^ 2)) ∣ p * (a ^ 2 + a * b + b ^ 2) := by
      rw [<-h₁]
      apply Nat.dvd_mul_left
    -- We have (a + b)(a² + b²) and (a² + ab + b²) coprime, so (a + b)(a² + b²) ∣ p.
    rw [Nat.Coprime.dvd_mul_right (Nat.Coprime.mul hab' hab''), Nat.dvd_prime hp] at h₁
    -- In either case, we have a + b = 1.
    replace h₁ : a + b = 1 := by
      cases h₁ with
      | inl h₁ =>
        simp at h₁
        tauto
      | inr h₁ =>
        rw [<-h₁, Nat.prime_mul_iff] at hp
        rcases hp with (⟨this, _⟩ | ⟨this, _⟩)
        . apply Nat.Prime.two_le at this
          linarith [show a + b ≤ a ^ 2 + b ^ 2 by apply add_le_add <;> apply Nat.le_self_pow (by norm_num)]
        . simp_all
    -- We can consider cases on a + b = 1.
    replace h₁ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
      omega
    rcases h₁ with (⟨ha', hb'⟩ | ⟨ha', hb'⟩)
    . -- We have (a, b, p) = (0, p, p).
      right
      use p, hp
      simp_all
      norm_cast at h₀
      rw [show d ^ 4 = d * d ^ 3 by ring] at h₀
      rw [Nat.mul_left_inj] at h₀
      exact h₀.symm
      simp [hd]
    . -- We have (a, b, p) = (p, 0, p).
      left
      use p, hp
      simp_all
      norm_cast at h₀
      rw [show d ^ 4 = d * d ^ 3 by ring] at h₀
      rw [Nat.mul_left_inj] at h₀
      exact h₀.symm
      simp [hd]
  . -- Now show that (x, y, p) = (0, p, p) or (p, 0, p) do satisfy the condition.
    rintro (⟨q, hq, h₀, h₁, h₂⟩ | ⟨q, hq, h₀, h₁, h₂⟩)
    <;> simp_all
    . simp [<-h₁, (Nat.Prime.pos hq).ne']
      ring
    . simp [<-h₀, (Nat.Prime.pos hq).ne'.symm]
      ring
