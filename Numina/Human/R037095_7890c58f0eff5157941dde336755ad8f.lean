import Mathlib

/- Determine all prime numbers $p$ and all positive integers $x$ and $y$ satisfying $x^{3}+y^{3}=$ $p(x y+p)$. -/
theorem number_theory_606196 : {(p, x, y) : ℤ × ℤ × ℤ | (p > 0) ∧ (Prime p) ∧ (0 < x) ∧ (0 < y) ∧
    (x ≤ y) ∧ (x^3 + y^3 = p * (x * y + p))} = {(19, 1, 8), (13, 2, 7), (7, 4, 5)} := by
    apply Set.ext
    intro (p, x, y)
    simp
    constructor
    intro ⟨hp1,hp2,hx,hy,hxy,hxyp⟩
    -- Set $s=x+y$. Rewrite the equation in the form $s\left(s^{2}-3 x y\right)=p(p+x y)$,
    let s := x + y
    have hs : s * (s ^ 2 - 3 * x * y) = p * (x * y + p) := by
      rw [← hxyp] ;simp [s] ;ring
    -- and express $x y$ :
    -- $$ x y=\frac{s^{3}-p^{2}}{3 s+p} $$
    have hxy' : x * y * (3 * s + p) = (s ^ 3 - p ^ 2) := by
      have : s ^ 3 = s * (s ^ 2) := by ring
      have this' : s * (s ^ 2) = s * (3 * x * y) + p * (x * y + p):= by
        rw [mul_sub] at hs ;exact Eq.symm (add_eq_of_eq_sub' (id (Eq.symm hs)))
      rw [this,this']
      have : (s * (3 * x * y) + p * (x * y + p) - p ^ 2) = (3 * s + p) * (x * y) := by ring
      rw [this] ;ring
    -- In particular,
    -- $$ s^{2} \geq 4 x y=\frac{4\left(s^{3}-p^{2}\right)}{3 s+p} $$
    -- or
    -- $$ (s-2 p)\left(s^{2}+s p+2 p^{2}\right) \leq p^{2}-p^{3}&lt;0 $$
    -- so $s&lt;2 p$.
    have h1 : s ^ 2 ≥ 4 * x * y := by
      have : s ^ 2 - 4 * x * y ≥ 0 := by
        have : s ^ 2 - 4 * x * y = (x - y) ^ 2 := by ring
        rw [this] ;exact sq_nonneg (x - y)
      exact four_mul_le_pow_two_add x y
    have h2 : s ^ 2 * (3 * s + p) ≥ 4 * x * y * (3 * s + p) := by
      refine Int.mul_le_mul_of_nonneg_right h1 (by nlinarith)
    rw [mul_assoc 4,mul_assoc,hxy'] at h2
    have h3 : (s - 2 * p) * (s ^ 2 + s * p + 2 * p ^ 2) ≤ 4 * (p ^ 2 - p ^ 3) := by
      have : 4 * (p ^ 2 - p ^ 3) - (s - 2 * p) * (s ^ 2 + s * p + 2 * p ^ 2) =
        s ^ 2 * (3 * s + p) - 4 * (s ^ 3 - p ^ 2) := by ring
      have this' : s ^ 2 * (3 * s + p) - 4 * (s ^ 3 - p ^ 2) ≥ 0 := by exact Int.sub_nonneg_of_le h2
      rw [← this] at this'
      exact Int.le_of_sub_nonneg this'
    have h4 : s < 2 * p := by
      have : p ^ 2 - p ^ 3 < 0 := by
        have : p ^ 2 - p ^ 3 = p ^ 2 * (1 - p) := by ring
        rw [this]
        have : 1 < p := by
          by_contra! ;interval_cases p
          have : Nat.Prime 1 := by exact Nat.prime_iff_prime_int.mpr hp2
          norm_num at this
        nlinarith
      have this' : 0 < (s ^ 2 + s * p + 2 * p ^ 2) := by nlinarith
      have : (s - 2 * p) < 0 := by nlinarith
      exact Int.lt_of_sub_neg this
    --  If $p \mid s$, then $s=p$ and $x y=p(p-1) / 4$ which is impossible for $x+y=p$ (the equation $t^{2}-p t+p(p-1) / 4=0$ has no integer solutions).
    by_cases hps : p ∣ s
    · have h5 : p = s := by
        have : ∃ k , s = k * p := exists_eq_mul_left_of_dvd hps
        rcases this with ⟨k, hk⟩
        have : k > 0 := by simp [s] at hk ;nlinarith
        rw [hk] at h4
        have this' : k < 2 := by nlinarith
        interval_cases k ;rw [hk] ;simp
      rw [← h5,← one_mul (p^2)] at hxy'
      nth_rewrite 2 [← one_mul p] at hxy'
      rw [← add_mul,pow_three,pow_two,← sub_mul,← mul_assoc,← mul_assoc] at hxy'
      norm_num at hxy'
      rcases hxy' with hxy' |hxy'
      have h6 : p ∣ (x * y * 4) := by rw [hxy'] ;exact Int.dvd_mul_left (p - 1) p
      apply Prime.dvd_or_dvd hp2 at h6
      rcases h6 with h6 | h6
      apply Prime.dvd_or_dvd hp2 at h6
      rcases h6 with h6 | h6
      · have : p ≤ x := by exact Int.le_of_dvd hx h6
        rw [h5] at this ;simp [s] at this ;linarith
      · have : p ≤ y := by exact Int.le_of_dvd hy h6
        rw [h5] at this ;simp [s] at this ;linarith
      have : (4:ℤ) = 2^2 := rfl
      rw [this] at h6
      have : p ∣ 2 := by exact Prime.dvd_of_dvd_pow hp2 h6
      have : p ≤ 2 := by exact Int.le_of_dvd (by simp) this
      interval_cases p
      · have : Nat.Prime 1 := by exact Nat.prime_iff_prime_int.mpr hp2
        norm_num at this
      have : x < 2 := by rw [h5] ;simp [s] ;linarith
      have : y < 2 := by rw [h5] ;simp [s] ;linarith
      interval_cases x ;interval_cases y ;norm_num at hxyp
      linarith
    -- If $p \nmid s$, rewrite $(\*)$ in the form
    -- $$ 27 x y=\left(9 s^{2}-3 s p+p^{2}\right)-\frac{p^{2}(p+27)}{3 s+p} $$
    have h7 : 27 * (x * y * (3 * s + p)) =
      (9 * s ^ 2 - 3 * s * p + p ^ 2) * (3 * s + p) - (p ^ 2 * (p + 27)) := by
      rw [hxy'] ;ring
    -- Since $p \nmid s$, this could be integer only if $3 s+p \mid$ $p+27$, and hence $3 s+p \mid 27-s$.
    have h8 : 3 * s + p ∣ p ^ 2 * (p + 27) := by
      have : 3 * s + p ∣ (9 * s ^ 2 - 3 * s * p + p ^ 2) * (3 * s + p) - p ^ 2 * (p + 27) := by
        rw [← h7,← mul_assoc] ;exact Int.dvd_mul_left (27 * (x * y)) (3 * s + p)
      have this' : 3 * s + p ∣ (9 * s ^ 2 - 3 * s * p + p ^ 2) * (3 * s + p) := by
        exact Int.dvd_mul_left (9 * s ^ 2 - 3 * s * p + p ^ 2) (3 * s + p)
      exact (Int.dvd_iff_dvd_of_dvd_sub this).mp this'
    rw [pow_two,mul_assoc] at h8
    have h9 : p ≠ 3 := by
      by_contra!
      rw [this] at h4 hxyp
      have : 0 < s := by nlinarith
      have : y < s := by simp [s] ;linarith
      interval_cases s
      <;> interval_cases y
      <;> interval_cases x
      <;> norm_num at hxyp
    have h10 : gcd (3 * s + p) p = 1 := by
      have : gcd (3 * s) p = gcd (3 * s + p) p := by refine Eq.symm (gcd_eq_of_dvd_sub_left ?_) ;simp
      have this' : IsCoprime p (3 * s) := by
        apply (Prime.coprime_iff_not_dvd hp2).mpr
        by_contra!
        apply Prime.dvd_or_dvd hp2 at this
        rcases this with this | this
        · have this' : p ≤ 3 := by exact Int.le_of_dvd (by simp) this
          interval_cases p
          · have : Nat.Prime 1 := by exact Nat.prime_iff_prime_int.mpr hp2
            norm_num at this
          norm_num at this
          exact h9 rfl
        exact hps this
      have this'' : IsCoprime (3 * s) p := by exact id (IsCoprime.symm this')
      apply Int.isCoprime_iff_gcd_eq_one.mp at this''
      have this''' : gcd (3 * s) p = (3 * s).gcd p := rfl
      rw [← this,this''',this''] ;simp
    have h11 : 3 * s + p ∣ p + 27 := by
      apply dvd_gcd_mul_iff_dvd_mul.mpr at h8
      rw [h10, one_mul] at h8
      apply dvd_gcd_mul_iff_dvd_mul.mpr at h8
      rw [h10, one_mul] at h8
      exact h8
    have h12 : 3 * s + p ∣ 27 - 3 * s := by
      have : 27 - 3 * s = p + 27 - (3 * s + p) := by ring
      rw [this] ;exact dvd_sub_self_right.mpr h11
    -- If $s \neq 9$, then $|3 s-27| \geq 3 s+p$, so $27-3 s \geq$ $3 s+p$, or $27-p \geq 6 s$, whence $s \leq 4$. These cases are ruled out by hand.
    have h13 : s ≤ 9 := by
      have : 3 * s + p ≤ p + 27 := Int.le_of_dvd (by linarith) h11
      rw [add_comm] at this ;simp at this ;omega
    apply Int.le_iff_lt_or_eq.mp at h13
    rcases h13 with h13 | h13
    · have h14 : 3 * s + p ≤ 27 - 3 * s := Int.le_of_dvd (by linarith) h12
      have h15 : s ≤ 4 := by omega
      have : 0 < s := by simp [s] ;linarith
      have : y < s := by simp [s] ;linarith
      interval_cases s
      · linarith
      · interval_cases y ;nlinarith
      · interval_cases y
        · interval_cases x ;omega
        norm_num at h12
        have : p ≤ 9 := by omega
        interval_cases p
        <;> omega
      interval_cases y
      <;> interval_cases x <;>omega
    -- If $s=x+y=9$, then $(\*)$ yields $x y=27-p$. Up to a swap of $x$ and $y$, all such triples $(x, y, p)$ are $(1,8,19),(2,7,13)$, and $(4,5,7)$.
    have : y < 9 := by rw [← h13] ;simp [s] ;linarith
    have this' : p ^ 2 < x ^ 3 + y ^ 3 := by
      rw [hxyp,mul_add,pow_two] ;simp
      refine Int.mul_pos hp1 (Int.mul_pos hx hy)
    have this'' : p ^ 2 < 1024 := by nlinarith
    have hp' : p < 32 := by nlinarith
    have hp' : p ∈ ({5,7,11,13,17,19,23,29,31} : Set ℤ) := by
      interval_cases p
      <;> norm_num at hp2
      <;> simp
      · interval_cases y
        <;> interval_cases x
        <;> omega
      linarith
    simp at hp'
    rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp'
    <;> rw [hp'] at hxyp
    <;> interval_cases y
    <;> interval_cases x
    <;> norm_num at hxyp
    <;> simp [hp']

    intro h
    rcases h with h | h | h
    <;> rw [h.1,h.2.1,h.2.2]
    <;> norm_num