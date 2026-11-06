import Mathlib

/- Trouver tous les entiers naturels non nuls $a, b$ et $c$ pour lesquels il existe des entiers naturels non nuls $x, y$ et $z$ tels que $x!=a b+1, y!=b c+1$ et $z!=c a+1$.
Remarque : Pour tout entier naturel non nul $n$, l'entier $n!$ désigne le produit $1 \times 2 \times \cdots \times n$. -/
theorem number_theory_605359 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (∃ x y z : ℕ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ Nat.factorial x = a * b + 1 ∧ Nat.factorial y = b * c + 1 ∧ Nat.factorial z = c * a + 1) ↔
    ∃ k, k ≥ 2 ∧ ((a, b, c) = (1, 1, Nat.factorial k - 1) ∨
         (a, b, c) = (1, Nat.factorial k - 1, 1) ∨
         (a, b, c) = (Nat.factorial k - 1, 1))
    := by

  constructor
  . intro hxyz
    -- Without loss of generaliy, assume that $a \leq b \leq c$.
    wlog h : a ≤ b ∧ b ≤ c with H
    . simp at h
      by_cases g : a ≤ b
      . by_cases g' : a ≤ c
        . obtain cltb := h g
          obtain ⟨ z, y, x, ⟨ hz, hy, hx, hzf, hyf, hxf ⟩ ⟩ := hxyz
          have : (∃ x y z, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
                  x.factorial = a * c + 1 ∧ y.factorial = c * b + 1 ∧ z.factorial = b * a + 1) := by
            use x, y, z
            rw [mul_comm] at hzf hxf hyf
            omega
          replace H := H a c b ha hc hb this ⟨ g', le_of_lt cltb ⟩
          obtain ⟨ k, hk ⟩ := H
          use k
          aesop
        . simp at g'
          obtain ⟨ y, z, x, ⟨ hy, hz, hx, hyf, hzf, hxf ⟩ ⟩ := hxyz
          have : (∃ x y z, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
                  x.factorial = c * a + 1 ∧ y.factorial = a * b + 1 ∧ z.factorial = b * c + 1) := by
            use x, y, z
          replace H := H c a b hc ha hb this ⟨ le_of_lt g', g ⟩
          obtain ⟨ k, hk ⟩ := H
          use k
          aesop
      . simp at g
        by_cases g' : a ≤ c
        . obtain ⟨ x, z, y, ⟨ hx, hz, hy, hxf, hzf, hyf ⟩ ⟩ := hxyz
          have : (∃ x y z, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
                  x.factorial = b * a + 1 ∧ y.factorial = a * c + 1 ∧ z.factorial = c * b + 1) := by
            use x, y, z
            rw [mul_comm] at hzf hxf hyf
            omega
          replace H := H b a c hb ha hc this ⟨ le_of_lt g, g' ⟩
          obtain ⟨ k, hk ⟩ := H
          use k
          aesop
        . simp at g'
          by_cases g'' : b ≤ c
          . obtain ⟨ z, x, y, ⟨ hz, hx, hy, hzf, hxf, hyf ⟩ ⟩ := hxyz
            have : (∃ x y z, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
                    x.factorial = b * c + 1 ∧ y.factorial = c * a + 1 ∧ z.factorial = a * b + 1) := by
              use x, y, z
            replace H := H b c a hb hc ha this ⟨ g'', le_of_lt g' ⟩
            obtain ⟨ k, hk ⟩ := H
            use k
            aesop
          . simp at g''
            obtain ⟨ y, x, z, ⟨ hy, hx, hz, hyf, hxf, hzf ⟩ ⟩ := hxyz
            have : (∃ x y z, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
                    x.factorial = c * b + 1 ∧ y.factorial = b * a + 1 ∧ z.factorial = a * c + 1) := by
              use x, y, z
              rw [mul_comm] at hyf hxf hzf
              omega
            replace H := H c b a hc hb ha this ⟨ le_of_lt g'', le_of_lt g ⟩
            obtain ⟨ k, hk ⟩ := H
            use k
            aesop
    . -- Let $x,y,z$ be nonzero natural numbers such that
      -- $x! = ab + 1$, $y! = bc + 1$ and $z! = ca + 1$.
      obtain ⟨ x, y, z, ⟨ hx, hy, hz, hxf, hyf, hzf ⟩ ⟩ := hxyz
      -- We show that $(a, b, c) = (1, 1, k! - 1)$ when $k = z$.
      use z
      constructor
      . have : c * a + 1 ≥ 2 := by
          have age1 : a ≥ 1 := by omega
          have cge1 : c ≥ 1 := by omega
          nlinarith
        rw [← hzf] at this
        by_contra g
        simp at g
        have zeq1 : z = 1 := by omega
        rw [zeq1] at this
        simp at this
      . left
        -- Note that $x ≥ 2$.
        have : x ≥ 2 := by
          -- Indeed, since $a, b \geq 1$, we have $x! = ab + 1 \geq 2$.
          have : a * b + 1 ≥ 2 := by
            have age1 : a ≥ 1 := by omega
            have bge1 : b ≥ 1 := by omega
            nlinarith
          rw [← hxf] at this
          by_contra g
          simp at g
          have xeq1 : x = 1 := by omega
          rw [xeq1] at this
          simp at this
        by_cases g : x = 2
        . -- Suppose that $x = 2$.
          -- Then $(a, b, c) = (1, 1, z! - 1)$
          simp [g] at hxf
          simp [hxf.1, hxf.2] at hyf hzf ⊢
          rw [hzf]
          exact rfl

        . -- Suppose that $x \geq 3$.
          have hxbd : x ≥ 3 := by omega

          -- We show that this case is impossible.
          by_contra

          -- Note that $3 ∣ x!$
          have dvd3x : 3 ∣ x.factorial := by
            apply Nat.dvd_factorial
            repeat linarith

          -- Hence, $a b \equiv -1 pmod 3$.
          have hab : a * b ≡ -1 [ZMOD 3] := by
            symm
            apply Int.modEq_of_dvd
            simp
            norm_cast
            rw [hxf] at dvd3x
            exact dvd3x

          -- Note that $3 ∣ y!$
          have dvd3y : 3 ∣ y.factorial := by
            apply Nat.dvd_factorial
            . norm_num
            . suffices x ≤ y by omega
              by_cases ac : a = c
              . rw [← ac] at hyf
                have : x.factorial = y.factorial := by
                  ring_nf at hyf hxf
                  simp [hyf, hxf]
                rw [Nat.factorial_inj] at this
                repeat linarith
              . have : a < c := by omega
                have : x.factorial < y.factorial := by
                  ring_nf at hyf hxf
                  simp [hyf, hxf]
                  apply Nat.mul_lt_mul_of_pos_left this
                  omega
                rw [Nat.factorial_lt] at this
                . exact Nat.le_of_succ_le this
                . omega

          -- Hence, $b c \equiv -1 pmod 3$.
          have hbc : b * c ≡ -1 [ZMOD 3] := by
            symm
            apply Int.modEq_of_dvd
            simp
            norm_cast
            rw [hyf] at dvd3y
            exact dvd3y

          -- Note that $3 ∣ z!$
          have dvd3z : 3 ∣ z.factorial := by
            apply Nat.dvd_factorial
            . norm_num
            . suffices x ≤ z by omega
              by_cases bc : b = c
              . rw [← bc] at hzf
                have : x.factorial = z.factorial := by
                  ring_nf at hzf hxf
                  simp [hxf, hzf]
                rw [Nat.factorial_inj] at this
                repeat omega
              . have : b < c := by omega
                have : x.factorial < z.factorial := by
                  ring_nf at hzf hxf
                  simp [hzf, hxf]
                  rw [mul_comm c]
                  apply Nat.mul_lt_mul_of_pos_left this
                  omega
                rw [Nat.factorial_lt] at this
                . exact Nat.le_of_succ_le this
                . omega

          -- Hence, $c a \equiv -1 pmod 3$.
          have hac : c * a ≡ -1 [ZMOD 3] := by
            symm
            apply Int.modEq_of_dvd
            simp
            norm_cast
            rw [hzf] at dvd3z
            exact dvd3z

          -- It follows that $(abc)^2 \equiv -1 pmod 3$.
          have habc : -1 ≡ (a * b * c)^2 [ZMOD 3] := by
            symm
            calc
              _ = (↑a * ↑b) * (↑b * ↑c) * (↑c * ↑a) := by ring
              _ ≡ (↑a * ↑b) * (↑b * ↑c) * (-1) [ZMOD 3] := by apply Int.ModEq.mul_left; exact hac
              _ = (-1) * (↑a * ↑b) * (↑b * ↑c) := by ring
              _ ≡ (-1) * (↑a * ↑b) * (-1) [ZMOD 3] := by apply Int.ModEq.mul_left; exact hbc
              _ = (-1) * (-1) * (↑a * ↑b) := by ring
              _ ≡ (-1) * (-1) * (-1) [ZMOD 3] := by apply Int.ModEq.mul_left; exact hab
              _ ≡ -1 [ZMOD 3] := by norm_num

          -- But for all $k \in ℕ$, we must have $k^2 \equiv 0 pmod 3$ or $k^2 \equiv 1 pmod 3$
          have sqmod3 (k : ℕ) : k ^ 2 ≡ 0 [ZMOD 3] ∨ k ^ 2 ≡ 1 [ZMOD 3] := by
            mod_cases (k : ℤ) % 3
            . left
              have : (k : ℤ) ^ 2 ≡ 0 ^ 2 [ZMOD 3] := by exact Int.ModEq.pow 2 H
              simpa [this]
            . right
              have : (k : ℤ) ^ 2 ≡ 1 ^ 2 [ZMOD 3] := by exact Int.ModEq.pow 2 H
              simpa [this]
            . right
              have : (k : ℤ) ^ 2 ≡ 2 ^ 2 [ZMOD 3] := by exact Int.ModEq.pow 2 H
              simpa [this]

          -- We therefore have a contradiction.
          obtain bad | bad := sqmod3 (a * b * c)
          . have : -1 ≡ 0 [ZMOD 3] := by exact Int.ModEq.trans habc bad
            revert this
            decide
          . have : -1 ≡ 1 [ZMOD 3] := by exact Int.ModEq.trans habc bad
            revert this
            decide
  . intro h
    obtain ⟨ k, ⟨ klb, hk ⟩  ⟩ := h
    obtain g | g | g := hk
    . use 2, k, k
      simp
      have hav : a = 1 := by aesop
      have hbv : b = 1 := by aesop
      have hcv : c = k.factorial - 1 := by aesop
      simp [hav, hbv, hcv]
      constructor
      . omega
      . refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
        refine Nat.one_le_iff_ne_zero.mpr ?_
        apply Nat.factorial_ne_zero
    . use k, k, 2
      simp
      have hav : a = 1 := by aesop
      have hbv : b = k.factorial - 1 := by aesop
      have hcv : c = 1 := by aesop
      simp [hav, hbv, hcv]
      constructor
      . omega
      . refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
        refine Nat.one_le_iff_ne_zero.mpr ?_
        apply Nat.factorial_ne_zero
    . use k, 2, k
      simp
      have hav : a = k.factorial - 1 := by aesop
      have hbv : b = 1 := by aesop
      have hcv : c = 1 := by aesop
      simp [hav, hbv, hcv]
      constructor
      . omega
      . refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
        refine Nat.one_le_iff_ne_zero.mpr ?_
        apply Nat.factorial_ne_zero
