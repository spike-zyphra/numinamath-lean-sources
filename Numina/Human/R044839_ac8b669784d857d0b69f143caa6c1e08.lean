import Mathlib

/-Trouver tous les entiers strictement positifs $a, b$ et $c$ tels que $\operatorname{PGCD}(a, b, c)=1$,

$$
a\left|(b-c)^{2}, \quad b\right|(a-c)^{2}, \quad c \mid(a-b)^{2}
$$

et tels qu'il est possible de construire un triangle non aplati dont les côtés ont pour longueurs $\mathrm{a}, \mathrm{b}$ et c .-/
theorem number_theory_607685 (a b c : ℕ) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c) :
Multiset.gcd {a, b, c} = 1 ∧ (a : ℤ) ∣ (b - c) ^ 2 ∧ (b : ℤ) ∣ (a - c) ^ 2 ∧ (c : ℤ) ∣ (a - b) ^ 2 ∧
a < b + c ∧ b < c + a ∧ c < a + b ↔ (a = 1 ∧ b = 1 ∧ c = 1) := by
  constructor
  -- Introduce assumptions and simplify the assumption hgcd
  · rintro ⟨hgcd, advd, bdvd, cdvd, alt, blt, clt⟩; simp [gcd_eq_nat_gcd] at hgcd
  -- Assume w. l. o. g. that $a$ is less or equal to $b$
    wlog aleb : a ≤ b
    · rw [show ((a:ℤ)-b)^2 = (b-a)^2 by ring] at cdvd; rw [add_comm] at alt blt clt
      rw [← Nat.gcd_assoc] at hgcd; nth_rw 2 [Nat.gcd_comm] at hgcd; rw [Nat.gcd_assoc] at hgcd
      specialize this b a c bpos apos cpos bdvd advd cdvd blt alt clt hgcd (show _ by linarith)
      split_ands; all_goals linarith
  -- Assume w. l. o. g. that $a$ is less or equal to $c$
    wlog alec : a ≤ c
    · rw [show ((a:ℤ)-c)^2 = (c-a)^2 by ring] at bdvd; rw [show ((a:ℤ)-b)^2 = (b-a)^2 by ring] at cdvd
      rw [show ((b:ℤ)-c)^2 = (c-b)^2 by ring] at advd; rw [add_comm] at alt blt clt
      rw [Nat.gcd_comm] at hgcd; nth_rw 2 [Nat.gcd_comm] at hgcd; rw [Nat.gcd_assoc] at hgcd
      specialize this c b a cpos bpos apos cdvd bdvd advd clt blt alt hgcd (show _ by linarith) (show _ by linarith)
      split_ands; all_goals linarith
  -- Assume w. l. o. g. that $b$ is less or equal to $c$
    wlog blec : b ≤ c
    · rw [show ((b:ℤ)-c)^2 = (c-b)^2 by ring] at advd; rw [add_comm] at alt blt clt
      nth_rw 2 [Nat.gcd_comm] at hgcd
      specialize this a c b apos cpos bpos advd cdvd bdvd alt clt blt hgcd alec aleb (show _ by linarith)
      split_ands; all_goals linarith
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
  -- Split the goal to two cases : $a < b$ and $a = b$
    rw [Nat.le_iff_lt_or_eq] at aleb; rcases aleb with altb|aeqb
    -- If $a < b$, show that it suffices to prove $a*b$ divides $(a+b-c)^2$
    · rw [← Nat.coprime_iff_gcd_eq_one] at gcdab; suffices : a * b ∣ (a + b - c) ^ 2
      · apply Nat.le_of_dvd at this; suffices : b = c
        · simp [this] at gcdbc; split_ands; all_goals linarith
        rw [eq_iff_le_not_lt]; constructor; exact blec; intro
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
  -- If $a=b$, it is straightforward to get $a=1$, $b=1$ and $c=1$ from linarith
    simp [aeqb] at gcdab; split_ands; all_goals linarith
-- Conversely, plug in $a=1$, $b=1$ and $c=1$ to the goals and simplify
  rintro ⟨ha, hb, hc⟩; simp [ha, hb, hc]