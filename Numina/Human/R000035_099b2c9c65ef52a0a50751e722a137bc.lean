import Mathlib

/-- Auxiliary lemma : if $ab$ is a perfect square and $a$ and $b$ are coprime, then $a$ is also a perfect square.  -/
lemma isSquare_mul (a b : ℕ) (h1 : IsSquare (a * b)) (h2 : a.Coprime b) :
  IsSquare a := by
    have h3 : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 h2
    obtain ⟨c, hc⟩ := h1
    have : (a : ℤ) * b = c ^ 2 := by norm_cast; rwa [pow_two]
    obtain ⟨d, hd⟩ := Int.sq_of_coprime (a := a) (b := b) h3 this
    by_cases ha : a = 0
    · exact ⟨0, ha⟩
    · have ha : 0 < a := Nat.zero_lt_of_ne_zero ha
      rw [←Int.natCast_pos] at ha
      replace hd := (or_iff_left (by
        intro hh;
        have ha' : (a : ℤ) ≤ 0 := by rw [hh]; norm_num; exact sq_nonneg d
        have ha'' : (a : ℤ) < 0 := by linarith
        exact (not_le_of_lt ha'') <| Int.natCast_nonneg _)).1 hd
      exact ⟨d.natAbs, by
        rw [ ←Int.natCast_inj]
        simp [hd, pow_two]⟩

/-- Natural numbers $\( a \)$ and $\( b \)$ are such that $\( a^2 + b^2 + a \)$ is divisible by $\( ab \)$. Prove that $\( a \)$ is a perfect square.-/
theorem number_theory_4066 {a b : Nat} (h : a * b ∣ a ^ 2 + b ^ 2 + a) : IsSquare a := by
  obtain ⟨k, hk⟩ := exists_eq_mul_left_of_dvd h
  -- Since $ab$ divides $a^2+b^2+a$, it also divides each term individually. Thus, $a^2 + b^2 +a \equiv 0 \pmod{a}$. 
  have h0 : a ^ 2 + b ^ 2 + a ≡ 0 [MOD a] := by
    rw [hk]; refine Nat.modEq_zero_iff_dvd.mpr ?_; rw [mul_comm, mul_assoc]; exact
      Nat.dvd_mul_right a (b * k)
  -- Above equation reduces to : $b^2 \equiv 0 \pmod {a}$. 
  have h1 : b ^ 2 ≡ 0 [MOD a] := by
    rw [Nat.modEq_zero_iff_dvd] at *
    rw [add_assoc] at h0
    have h2 : a ∣ a ^ 2 := by simp [pow_two]
    have h3 := (Nat.dvd_add_right h2).1 h0
    exact (Nat.dvd_add_left <| Nat.dvd_refl a).1 h3
  have := Nat.ModEq.dvd h1
  simp at this; norm_cast at this
  obtain ⟨k, hk⟩ := this
  rw [hk] at h
  rw [show (a ^ 2 + a * k + a = a * (a + k + 1) ) by ring, ] at h
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  · have tmp : b ∣ a + k + 1 := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero ha) h
    have : a.Coprime k := by
      by_contra!
      have h2 : a.gcd k ≠ 1 := this
      obtain ⟨p, hp⟩ := Nat.ne_one_iff_exists_prime_dvd.1 h2
      have h3 : p ∣ a := hp.2.trans (Nat.gcd_dvd a k).1
      have h4 : p ∣ k := hp.2.trans (Nat.gcd_dvd a k).2
      have h5 : p ∣ b := by
        have : p ∣ b ^ 2:= h3.trans ⟨k, hk⟩
        exact Nat.Prime.dvd_of_dvd_pow hp.1 this
      have h6 := h5.trans tmp
      have : p ∣ 1 := (Nat.dvd_add_right ((Nat.dvd_add_right h3).2 h4) ).1 h6
      exact Nat.eq_one_iff_not_exists_prime_dvd.1 rfl p hp.1 this
    exact isSquare_mul a k ⟨b, by rw [←hk, pow_two] ⟩ this
