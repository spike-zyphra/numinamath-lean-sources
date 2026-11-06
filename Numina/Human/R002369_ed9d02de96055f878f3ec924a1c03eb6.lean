import Mathlib

/- Three prime numbers $p,q,r$ and a positive integer $n$ are given such that the numbers
 \frac{p+n}{qr}, \frac{q+n}{rp}, \frac{r+n}{pq}
are integers. Prove that $p=q=r $.
-/
theorem number_theory_89171 (p q r n : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hn : 0 < n) (h1 : q * r ∣ p + n) (h2 : r * p ∣ q + n)
    (h3 : p * q ∣ r + n) : p = q ∧ q = r := by
    -- we first prove the case for p ≥ q ≥ r
    have h: ∀ x y z m: ℕ, x ≤ y ∧ y ≤ z ∧ m > 0 ∧ x.Prime ∧ y.Prime ∧ z.Prime ∧ y * z ∣ x + m ∧ z * x ∣ y + m ∧
    x * y ∣ z + m → x = y ∧ y = z := by
      clear * -
      intro x y z m h
      rcases h with ⟨hxy, hyz, hm, hx, hy, hz, h1, h2, h3⟩
      have d1: z ∣ x + m := by
        have d: z ∣ y * z := by simp
        apply dvd_trans d h1
      have d2: z ∣ y + m := by
        have d: z ∣z * x := by simp
        apply dvd_trans d h2
      have l: z ∣ y - x := by
        rw [show y - x = y + m - (x + m) by omega]
        apply Nat.dvd_sub
        omega
        exact d2
        exact d1
      have i: y - x = 0 := by
        by_contra!
        replace i: 0 < y - x := by omega
        apply Nat.le_of_dvd at l
        have lx: 0 < x := by
          by_contra! no
          replace no: x = 0 := by omega
          rw [no] at hx
          absurd hx
          norm_num
        absurd l
        simp
        calc
          y - x < y := by omega
              _ ≤ z := by nlinarith
        exact i
      replace i: y = x := by omega
      simp [i] at *
      clear h2 hxy l i d2
      have d1: x ∣ x + m := by
        have d: x ∣ x * z := by simp
        apply Nat.dvd_trans d h1
      have d2: x ∣ z + m := by
        have d: x ∣ x * x := by simp
        apply Nat.dvd_trans d h3
      have l: x ∣ z - x := by
        rw [show z - x = z + m - (x + m) by omega]
        apply Nat.dvd_sub
        omega
        exact d2
        exact d1
      have d: x ∣ z := by
        rw [show z = x + (z - x) by omega]
        apply Nat.dvd_add
        simp
        exact l
      rw [Nat.Prime.dvd_iff_eq] at d
      . simp [d]
      . exact hz
      . by_contra! no
        rw [no] at hx
        absurd hx
        norm_num

    -- then we use the above lemma to prove all cases
    have c: r ≤ q ∧ q ≤ p ∨ r ≤ p ∧ p ≤ q ∨
     p ≤ r ∧ r ≤ q ∨ p ≤ q ∧ q ≤ r ∨
     q ≤ p ∧ p ≤ r ∨ q ≤ r ∧ r ≤ p := by omega

    rcases c with c | c | c | c | c | c
    -- r ≤ q ∧ q ≤ p
    . specialize h r q p n
      simp [*] at h
      rw [show q * p = p * q by ring] at h
      rw [show p * r = r * p by ring] at h
      rw [show r * q = q * r by ring] at h
      simp [*] at h
      simp [h]
    -- r ≤ p ∧ p ≤ q
    . specialize h r p q n
      simp [*] at h
      simp [h]
    -- p ≤ r ∧ r ≤ q
    . specialize h p r q n
      simp [*] at h
      rw [show r * q = q * r by ring] at h
      rw [show q * p = p * q by ring] at h
      rw [show p * r = r * p by ring] at h
      simp [*] at h
      simp [h]
    -- p ≤ q ∧ q ≤ r
    . specialize h p q r n
      simp [*] at h
      simp [h]
    -- q ≤ p ∧ p ≤ r
    . specialize h q p r n
      simp [*] at h
      rw [show p * r = r * p by ring] at h
      rw [show q * p = p * q by ring] at h
      rw [show r * q = q * r by ring] at h
      simp [*] at h
      simp [h]
    -- q ≤ r ∧ r ≤ p
    . specialize h q r p n
      simp [*] at h
      simp [h]