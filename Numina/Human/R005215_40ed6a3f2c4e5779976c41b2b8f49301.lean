import Mathlib

/- Let $x$ and $y$ be positive integers and assume that $z=4 x y /(x+y)$ is an odd integer. Prove that at least one divisor of $z$ can be expressed in the form $4 n-1$ where $n$ is a positive integer. -/
theorem number_theory_606313 (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (h : (x + y) ∣ (4 * x * y) ∧ Odd ((4 * x * y) / (x + y))) :
  ∃ d, d ∣ (4 * x * y) / (x + y) ∧ ∃ n, 0 < n ∧ d = 4 * n - 1 := by
  rcases h with ⟨⟨z,hz⟩,⟨n,hn⟩⟩
  have hz' : z = (4 * x * y) / (x + y) := by rw [hz] ;refine Nat.eq_div_of_mul_eq_right ?_ rfl ;linarith
  have : 0 < x + y := by linarith
  rw [hz,Nat.mul_div_cancel_left z this] at hn
  -- Let $x=2^{s} x_{1}$ and $y=2^{t} y_{1}$ where $x_{1}$ and $y_{1}$ are odd integers.
  have hx : ∃ (s : ℕ) (x₁ : ℕ), ¬2 ∣ x₁ ∧ x = 2 ^ s * x₁ := by
    apply Nat.exists_eq_pow_mul_and_not_dvd ;linarith ;simp
  rcases hx with ⟨s,x₁,⟨hx1,hx2⟩⟩
  have hy : ∃ (t : ℕ) (y₁ : ℕ), ¬2 ∣ y₁ ∧ y = 2 ^ t * y₁ := by
    apply Nat.exists_eq_pow_mul_and_not_dvd ;linarith ;simp
  rcases hy with ⟨t,y₁,⟨hy1,hy2⟩⟩
  -- Without loss of generality we can assume that $s \geq t$.
  by_cases hst : s ≥ t
  -- We have $$ z=\frac{2^{s+t+2} x_{1} y_{1}}{2^{t}\left(2^{s-t} x_{1}+y_{1}\right)}=\frac{2^{s+2} x_{1} y_{1}}{2^{s-t} x_{1}+y_{1}} $$
  have : s = s - t + t := by exact (Nat.sub_eq_iff_eq_add hst).mp rfl
  rw [hx2,hy2] at hz ;nth_rewrite 2 [this] at hz
  rw [Nat.pow_add,mul_comm (2 ^ (s - t)),mul_assoc (2 ^ t),← mul_add,mul_comm,mul_assoc,mul_assoc] at hz
  simp at hz
  -- If $s \neq t$, then the denominator is odd and therefore $z$ is even.
  by_cases hst' : s ≠ t
  have hst'' : t < s := by exact Nat.lt_of_le_of_ne hst (id (Ne.symm hst'))
  have hz' : Even ((2 ^ (s - t) * x₁ + y₁) * z) := by
    rw [← hz] ;use y₁ * (2 * (2 ^ s * x₁)) ;ring_nf
  have hz'' : Even z := by
    rcases Nat.even_mul.mp hz' with h' |h'
    · have h1 : Even (2 ^ (s - t) * x₁) := by
        use (2 ^ (s - t - 1) * x₁) ;ring_nf ;nth_rewrite 3 [← pow_one 2] ;rw [mul_assoc,← pow_add,Nat.sub_add_cancel]
        exact Nat.le_sub_of_add_le' hst''
      apply (Nat.even_add.mp h').mp at h1
      have h2 : 2 ∣ y₁ := by exact even_iff_two_dvd.mp h1
      exact False.elim (hy1 h2)
    exact h'
  apply Nat.not_odd_iff_even.mpr at hz''
  have : Odd z := by refine Nat.odd_iff.mpr ?_ ;rw [hn,Nat.add_mod] ;simp
  exact False.elim (hz'' this)
  -- So we have $s=t$ and $z=2^{s+2} x_{1} y_{1} /\left(x_{1}+y_{1}\right)$.
  push_neg at hst'
  simp [← hst'] at hz
  -- Let $x_{1}=d x_{2}, y_{1}=d y_{2}$ with $\operatorname{gcd}\left(x_{2}, y_{2}\right)=1$.
  have hx3 : gcd x₁ y₁ ∣ x₁ := by exact gcd_dvd_left x₁ y₁
  rcases hx3 with ⟨x₂,hx3⟩
  have hy3 : gcd x₁ y₁ ∣ y₁ := by exact gcd_dvd_right x₁ y₁
  rcases hy3 with ⟨y₂,hy3⟩
  have hgcd : gcd x₁ y₁ = gcd x₁ y₁ * x₂.gcd y₂ := by rw [← Nat.gcd_mul_left (gcd x₁ y₁) x₂ y₂,← hx3,← hy3] ;rfl
  -- So $z=$ $2^{s+2} d x_{2} y_{2} /\left(x_{2}+y_{2}\right)$.
  rw [hx3] at hz ;nth_rewrite 1 4 [hy3] at hz ;rw [← mul_add,mul_assoc,mul_assoc] at hz ;simp at hz
  have : x₁ ≠ 0 := by by_contra! h ;rw [h,mul_zero] at hx2 ;linarith
  simp [this] at hz
  -- As $z$ is odd, it must be that $x_{2}+y_{2}$ is divisible by $2^{s+2} \geq 4$, so $x_{2}+y_{2}$ is divisible by 4.
  have dvd1 : 4 * (2 ^ s) ∣ (x₂ + y₂) * z := by rw [← hz] ;ring_nf ;rw [mul_assoc] ;simp
  have nedvd : gcd (4 * (2 ^ s)) z = 1 := by
    have : 4 * (2 ^ s) = 2 ^ (2 + s) := by ring
    rw [this]
    have : z.Coprime (2 ^ (2 + s)) := by
      apply Nat.Prime.coprime_pow_of_not_dvd
      exact Nat.prime_two
      refine Nat.two_dvd_ne_zero.mpr ?_
      rw [hn,Nat.add_mod] ;simp
    apply Nat.Coprime.gcd_eq_one
    exact Nat.coprime_comm.mp this
  have dvd2 : 4 * (2 ^ s) ∣ x₂ + y₂ := by exact Nat.Coprime.dvd_of_dvd_mul_right nedvd dvd1
  have dvd3 : 4 ∣ x₂ + y₂ := by exact dvd_of_mul_right_dvd dvd2
  -- As $x_{2}$ and $y_{2}$ are odd integers, one of them, say $x_{2}$ is congruent to 3 modulo 4.
  have hxy2 : x₂ % 4 = 3 ∨ y₂ % 4 = 3 := by
    by_contra! h
    have h1 : x₂ % 4 = 1 := by
      have : x₂ % 2 = 1 := by
        refine Nat.mod_two_ne_zero.mp ?_
        by_contra! h'
        have : x₁ % 2 = 0 := by rw [hx3,Nat.mul_mod,h'] ;simp
        have : 2 ∣ x₁ := by exact Nat.dvd_of_mod_eq_zero this
        exact False.elim (hx1 this)
      apply Nat.odd_mod_four_iff.mp at this
      simp [h] at this
      exact this
    have h2 : y₂ % 4 = 1 := by
      have : y₂ % 2 = 1 := by
        refine Nat.mod_two_ne_zero.mp ?_
        by_contra! h'
        have : y₁ % 2 = 0 := by rw [hy3,Nat.mul_mod,h'] ;simp
        have : 2 ∣ y₁ := by exact Nat.dvd_of_mod_eq_zero this
        exact False.elim (hy1 this)
      apply Nat.odd_mod_four_iff.mp at this
      simp [h] at this
      exact this
    have h3 : (x₂ + y₂) % 4 = 0 := by exact Nat.dvd_iff_mod_eq_zero.mp dvd3
    rw [Nat.add_mod,h1,h2] at h3 ;simp at h3
  -- But $\operatorname{gcd}\left(x_{2}, x_{2}+y_{2}\right)=1$, so $x_{2}$ is a divisor of $z$.
  have dvd4 : x₂ ∣ (x₂ + y₂) * z ∧ y₂ ∣ (x₂ + y₂) * z := by
    rw [← hz] ;simp ;ring_nf ;rw [mul_comm (y₂ * gcd x₁ y₁),mul_assoc,mul_assoc] ;simp
  have hgcd' : gcd x₂ (x₂ + y₂) = 1 ∧ gcd y₂ (x₂ + y₂) = 1 := by
    have : x₂.gcd y₂ = 1 := by
      symm at hgcd
      apply mul_right_eq_self₀.mp at hgcd
      rcases hgcd with h | h
      · exact h
      simp at h ;rw [h.1,mul_zero] at hx2 ;linarith
    constructor
    · rw [← this,← Nat.gcd_add_self_right,add_comm] ;rfl
    rw [← this,← Nat.gcd_add_self_left,Nat.gcd_comm] ;rfl
  have dvd5 : x₂ ∣ z ∧ y₂ ∣ z := by
    constructor
    have : x₂.Coprime (x₂ + y₂) := by exact hgcd'.1
    apply Nat.Coprime.dvd_of_dvd_mul_right this
    rw [mul_comm] ;exact dvd4.1
    have : y₂.Coprime (x₂ + y₂) := by exact hgcd'.2
    apply Nat.Coprime.dvd_of_dvd_mul_right this
    rw [mul_comm] ;exact dvd4.2
  rw [← hz']
  rcases hxy2 with hxy2 | hxy2
  · use x₂ ;simp [dvd5]
    use (x₂ / 4 + 1) ;simp
    have : x₂ = 4 * (x₂ / 4) + x₂ % 4 := by exact Eq.symm (Nat.div_add_mod x₂ 4)
    rw [this,hxy2] ;ring_nf ;rw [Nat.add_div_of_dvd_left] ;simp
    exact Eq.symm (Nat.succ_add_sub_one (x₂ / 4 * 4) 3) ;simp
  use y₂ ;simp [dvd5]
  use (y₂ / 4 + 1) ;simp
  have : y₂ = 4 * (y₂ / 4) + y₂ % 4 := by exact Eq.symm (Nat.div_add_mod y₂ 4)
  rw [this,hxy2] ;ring_nf ;rw [Nat.add_div_of_dvd_left] ;simp
  exact Eq.symm (Nat.succ_add_sub_one (y₂ / 4 * 4) 3) ;simp
  simp at hst
  -- Similarly
  have : t = t - s + s := by exact (Nat.sub_eq_iff_eq_add (by linarith)).mp rfl
  rw [hx2,hy2] at hz ;nth_rewrite 2 [this] at hz
  rw [Nat.pow_add,mul_comm (2 ^ (t - s)),mul_assoc (2 ^ s),← mul_add,mul_comm 4,mul_assoc,mul_assoc,mul_assoc] at hz
  simp at hz
  have hz' : Even ((x₁ + 2 ^ (t - s) * y₁) * z) := by
    rw [← hz] ;use (x₁ * (2 * (2 ^ t * y₁))) ;ring_nf
  have hz'' : Even z := by
    rcases Nat.even_mul.mp hz' with h' |h'
    · have h1 : Even (2 ^ (t - s) * y₁) := by
        use (2 ^ (t - s - 1) * y₁) ;ring_nf ;nth_rewrite 3 [← pow_one 2] ;rw [mul_assoc,← pow_add,Nat.sub_add_cancel]
        exact Nat.le_sub_of_add_le' hst
      apply (Nat.even_add.mp h').mpr at h1
      have h2 : 2 ∣ x₁ := by exact even_iff_two_dvd.mp h1
      exact False.elim (hx1 h2)
    exact h'
  apply Nat.not_odd_iff_even.mpr at hz''
  have : Odd z := by refine Nat.odd_iff.mpr ?_ ;rw [hn,Nat.add_mod] ;simp
  exact False.elim (hz'' this)
