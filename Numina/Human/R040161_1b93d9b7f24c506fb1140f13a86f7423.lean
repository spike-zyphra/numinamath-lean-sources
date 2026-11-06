import Mathlib

/- Three pairwise distinct positive integers $a, b, c$, with $\operatorname{gcd}(a, b, c)=1$, satisfy

$$
a\left|(b-c)^{2}, \quad b\right|(c-a)^{2} \quad \text { and } \quad c \mid(a-b)^{2} \text {. }
$$

Prove that there does not exist a non-degenerate triangle with side lengths $a, b, c$. -/
theorem number_theory_605745 : ¬ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
Multiset.gcd {a, b, c} = 1 ∧ (a : ℤ) ∣ (b - c) ^ 2 ∧ (b : ℤ) ∣ (c - a) ^ 2 ∧ (c : ℤ) ∣ (a - b) ^ 2 ∧
a < b + c ∧ b < c + a ∧ c < a + b := by
-- Assume the contrary that there exists such $a$, $b$ and $c$
  rintro ⟨a, b, c, apos, bpos, cpos, aneb, anec, bnec, hgcd, advd, bdvd, cdvd, alt, blt, clt⟩
-- Assume w. l. o. g. that $a$ is less than $b$
  simp [gcd_eq_nat_gcd] at hgcd; wlog altb : a < b
  · replace altb : b < a := by rw [lt_iff_le_and_ne]; constructor; linarith; exact Ne.symm aneb
    rw [← show ((a:ℤ)-c)^2 = (c-a)^2 by ring] at bdvd; rw [show ((b:ℤ)-c)^2 = (c-b)^2 by ring] at advd
    rw [show ((a:ℤ)-b)^2 = (b-a)^2 by ring] at cdvd; rw [add_comm] at alt blt clt
    rw [← Nat.gcd_assoc] at hgcd; nth_rw 2 [Nat.gcd_comm] at hgcd; rw [Nat.gcd_assoc] at hgcd
    specialize this b a c bpos apos cpos (Ne.symm aneb) bnec anec bdvd advd cdvd blt alt clt hgcd altb
    exact this
-- Assume w. l. o. g. that $a$ is less than $c$
  wlog altc : a < c
  · replace altc : c < a := by rw [lt_iff_le_and_ne]; constructor; linarith; exact Ne.symm anec
    rw [← show ((a:ℤ)-c)^2 = (c-a)^2 by ring] at bdvd; rw [show ((a:ℤ)-b)^2 = (b-a)^2 by ring] at cdvd
    rw [show ((b:ℤ)-c)^2 = (c-b)^2 by ring] at advd; rw [add_comm] at alt blt clt
    rw [Nat.gcd_comm] at hgcd; nth_rw 2 [Nat.gcd_comm] at hgcd; rw [Nat.gcd_assoc] at hgcd
    specialize this c b a cpos bpos apos (Ne.symm bnec) (Ne.symm anec) (Ne.symm aneb) cdvd bdvd advd clt blt alt hgcd (show _ by linarith) altc
    exact this
-- Assume w. l. o. g. that $b$ is less than $c$
  wlog bltc : b < c
  · replace bltc : c < b := by rw [lt_iff_le_and_ne]; constructor; linarith; exact Ne.symm bnec
    rw [show ((b:ℤ)-c)^2 = (c-b)^2 by ring] at advd; rw [show ((a:ℤ)-b)^2 = (b-a)^2 by ring] at cdvd
    rw [← show ((a:ℤ)-c)^2 = (c-a)^2 by ring] at bdvd; rw [add_comm] at alt blt clt
    nth_rw 2 [Nat.gcd_comm] at hgcd
    specialize this a c b apos cpos bpos anec aneb (Ne.symm bnec) advd cdvd bdvd alt clt blt hgcd altc altb bltc
    exact this
  rw [← show ((a:ℤ)-c)^2 = (c-a)^2 by ring] at bdvd
-- Prove that the gcd of $a$ and $b$ is $1$
  have gcdab : a.gcd b = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]; intro p ppr pdvd; have := ppr.two_le
    rw [Nat.dvd_gcd_iff] at pdvd; suffices : p ∣ a.gcd (b.gcd c)
    · rw [hgcd] at this; simp at this; linarith
    simp [Nat.dvd_gcd_iff]; split_ands; exact pdvd.left; exact pdvd.right
    suffices : p ∣ c ^ 2; apply Nat.Prime.dvd_of_dvd_pow ppr this
    zify; have : (p : ℤ) ∣ (b - c) ^ 2 := by apply dvd_trans _ advd; norm_cast; exact pdvd.left
    rw [← dvd_sub_right this, sq_sub_sq]; simp; rw [Prime.dvd_mul]; left
    norm_cast; exact pdvd.right; rw [← Nat.prime_iff_prime_int]; exact ppr
  -- Prove that the gcd of $b$ and $c$ is $1$
  have gcdbc : b.gcd c = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]; intro p ppr pdvd; have := ppr.two_le
    rw [Nat.dvd_gcd_iff] at pdvd; suffices : p ∣ a.gcd (b.gcd c)
    · rw [hgcd] at this; simp at this; linarith
    simp [Nat.dvd_gcd_iff]; split_ands
    · suffices : p ∣ a ^ 2; apply Nat.Prime.dvd_of_dvd_pow ppr this
      zify; have : (p : ℤ) ∣ (a - c) ^ 2 := by apply dvd_trans _ bdvd; norm_cast; exact pdvd.left
      rw [← dvd_sub_right this, sq_sub_sq]; simp; rw [Prime.dvd_mul]; right
      norm_cast; exact pdvd.right; rw [← Nat.prime_iff_prime_int]; exact ppr
    exact pdvd.left; exact pdvd.right
-- Show that it suffices to prove $a*b$ divides $(a+b-c)^2$
  rw [← Nat.coprime_iff_gcd_eq_one] at gcdab; suffices : a * b ∣ (a + b - c) ^ 2
  · apply Nat.le_of_dvd at this; suffices : b = c
    · simp [this] at gcdbc; all_goals linarith
    rw [eq_iff_le_not_lt]; constructor; linarith; intro
    suffices : (a + b - c) ^ 2 < a * b; linarith
    rw [pow_two]; apply mul_lt_mul; rw [Nat.sub_lt_iff_lt_add]; any_goals linarith
    rw [Nat.sub_le_iff_le_add]; linarith; rw [Nat.sub_pos_iff_lt]; exact clt
    apply Nat.pow_pos; rw [Nat.sub_pos_iff_lt]; exact clt
-- Since $a$ and $b$ are coprime, it suffices to show they divide $(a+b-c)^2$ seperately
  apply gcdab.mul_dvd_of_dvd_of_dvd; zify; rw [Nat.cast_sub]; push_cast
  rw [add_sub_assoc,add_sq]; apply dvd_add; apply dvd_add; apply dvd_pow_self; simp
  rw [mul_comm, ← mul_assoc]; simp; exact advd; linarith
  zify; rw [add_comm, Nat.cast_sub]; push_cast
  rw [add_sub_assoc,add_sq]; apply dvd_add; apply dvd_add; apply dvd_pow_self; simp
  rw [mul_comm, ← mul_assoc]; simp; exact bdvd; linarith