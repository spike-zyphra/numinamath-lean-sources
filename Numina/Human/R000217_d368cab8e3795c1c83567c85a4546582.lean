import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find the triplets of primes  $(a,\ b,\ c)$  such that  $a-b-8$  and  $b-c-8$  are primes.-/
theorem number_theory_8596 :
  {(a, b, c) : ℕ × ℕ × ℕ | a.Prime ∧ b.Prime ∧ c.Prime ∧
  (a - b - 8).Prime ∧ (b - c - 8).Prime} = {(23, 13, 2), (23, 13, 3)} := by
    ext x
    simp
    -- In this proof, `x.1`, `x.2.1` and `x.2.2` means $a$, $b$ and $c$ respectively.
    set a := x.1   with ha
    set b := x.2.1 with hb
    set c := x.2.2 with hc
    -- An auxiliary lemma : if for three numbers $a, b, c$ exists a number $x$ such that
    -- $a \equiv x \pmod3$, $b \equiv x + 1\pmod3$ and $c \equiv x + 2\pmod3$, 3 divides one
    -- of $a, b, c$.
    have aux (a b c x) : a ≡ x [MOD 3] ∧ b ≡ x + 1 [MOD 3] ∧ c ≡ x + 2 [MOD 3] →
      3 ∣ a ∨ 3 ∣ b ∨ 3 ∣ c := by
        have h1 : x % 3 < 3 := mod_lt x (by omega)
        have h2 : x ≡ x % 3 [MOD 3] := (mod_modEq x 3).symm
        intro ⟨ha, hb, hc⟩
        interval_cases x % 3
        · have : a ≡ 0 [MOD 3] := ha.trans h2
          exact Or.inl <| dvd_of_mod_eq_zero this
        · have : c ≡ 0 [MOD 3] := hc.trans (Nat.ModEq.add h2 (Nat.ModEq.rfl (a := 2)))
          exact Or.inr <| Or.inr <| dvd_of_mod_eq_zero this
        · have : b ≡ 0 [MOD 3] := hb.trans (Nat.ModEq.add h2 (Nat.ModEq.rfl (a := 1)))
          exact Or.inr <| Or.inl <| dvd_of_mod_eq_zero this
    constructor
    · intro ⟨ap, bp, cp, abp, bcp⟩
      have := Nat.Prime.pos abp
      have := Nat.Prime.pos bcp
      -- Since  $a-b-8$  and  $b-c-8$  are both primes,  $a > b > c >= 2$
      have blta : b < a := by omega
      have cltb : c < b := by omega
      have cge2 : 2 ≤ c := Nat.Prime.two_le cp
      have oddab  : Odd a ∧ Odd b := ⟨Nat.Prime.odd_of_ne_two ap (by omega),
          Nat.Prime.odd_of_ne_two bp (by omega)⟩
      -- Clearly  $a$  and  $b$  are odd. Thus  $a-b-8$  is even and a prime,
      -- which implies that  $a-b-8 = 2$  or  $a = b+10$
      have c1   : a = b + 10 := by
        have evenab : Even (a - b - 8) := by
          apply (Nat.even_sub (show 8 ≤ a - b by omega)).2
          have : Even (a - b) := (Nat.even_sub' (by omega)).2 (by tauto)
          simp [this]
          decide
        have := (Nat.Prime.even_iff abp).1 evenab
        omega
      --Consider the cases  $c = 2$  and  $c$  is odd i.e. $2 < c$.
      rcases le_iff_lt_or_eq.1 cge2 with cgt2 | c2
      · have oddc := Nat.Prime.odd_of_ne_two cp (by omega)
        -- Since  $b$  and  $c$  are odd,  $b-c-8 = 2$  or  $b = c+10$.
        have c2 : b = c + 10 := by
          have evenbc : Even (b - c - 8) := by
            apply (Nat.even_sub (show 8 ≤ b - c by omega)).2
            have : Even (b - c) := (Nat.even_sub' (by omega)).2 (by tauto)
            simp [this]
            decide
          have := (Nat.Prime.even_iff bcp).1 evenbc
          omega
        simp [c2] at c1
        --  So  $c$ ,  $b = c+10$  and  $a = b+10 = c+20$  are all odd primes.
        --  Under modulo 3, we have  $a = c-1$ ,  $b = c+1$  and  $c$ .
        have amodc : a ≡ c + 2 [MOD 3] := by
          simp [c1, add_assoc]
          exact Nat.ModEq.add Nat.ModEq.rfl (by decide)
        have bmodc : b ≡ c + 1 [MOD 3] := by
          simp [c2]
          exact Nat.ModEq.add Nat.ModEq.rfl (by decide)
        -- Therefore at least one of  $a$ ,  $b$ ,  $c$  is divisible by 3 by the above lemma.
        have h1 := aux c b a c ⟨rfl, bmodc, amodc⟩
        have _ : 3 < b := by omega
        have _ : 3 < a := by omega
        -- It follows that  $a$ ,  $b$ ,  $c$  are all odd primes only if  $c = 3$ .
        -- Thus  $b = c+10 = 13$  and  $a= c+20 = 23$ . The only triplets of primes is
        -- $(a, b, c) = (23, 13, 3)$ .
        have h2 : 3 ∣ c := by
          refine (or_iff_left ?_ ).1 h1
          simp
          exact ⟨fun h => by have := (Nat.Prime.dvd_iff_eq bp (by omega)).1 h; omega,
            fun h => by have := (Nat.Prime.dvd_iff_eq ap (by omega)).1 h; omega⟩
        have c3 := (Nat.Prime.dvd_iff_eq cp (by omega)).1 h2
        simp [c3] at c1 c2
        right; ext <;> simpa
      · -- Case 2 : $c = 2$.
        -- In this case,  $a = b+10$ ,  $b$  and  $b-c-8 = b-10$  are all odd primes.
        have h1 : Odd (b - c - 8) := by
          by_contra evenbc8
          simp at evenbc8
          have := (Nat.Prime.even_iff bcp).1 evenbc8
          simp [←c2] at this
          have : b = 12 := by omega
          simp [this] at bp
          tauto
        replace _ := (show b - 10 = b - c - 8 by omega) ▸ h1
        replace bcp := (show b - 10 = b - c - 8 by omega) ▸ bcp
        -- Under modulo 3, we have  $a = b+1$ ,  $b$  and  $b-10 = b-1$ .
        have mod2 : b - 10 ≡ b + 2 [MOD 3] := (Nat.modEq_iff_dvd' (by omega)).2 (by omega)
        have mod1 : a ≡ b + 1 [MOD 3] := by
          simp [c1]
          exact Nat.ModEq.add Nat.ModEq.rfl (by decide)
        -- Therefore at least one of $a$, $b$ and $b-10$ is divisible by 3 by the above lemma.
        have := aux b a (b - 10) b ⟨rfl, mod1, mod2⟩
        -- It follows that  $a$ ,  $b$ ,  $b-10$  are all primes only if  $b-10 = 3$ .
        -- Thus  $b = 13$  and  $a = b+10 = 23$.
        have : 3 ∣ b - 10 := by
          refine (or_iff_right ?_).1 <| (or_iff_right ?_).1 this
          exact fun h => by have := (Nat.Prime.dvd_iff_eq ap (by omega)).1 h; omega
          exact fun h => by have := (Nat.Prime.dvd_iff_eq bp (by omega)).1 h; omega
        have : b = 13 := by
          have : 3 = b - 10 := ((Nat.Prime.dvd_iff_eq bcp (by omega)).1 this).symm
          omega
        simp [this] at c1
        left; ext <;> simp <;> omega
    · -- Verify $(a, b, c) = (23, 13, 2)$  and  $(23, 13, 3)$ are both solutions.
      intro h
      rcases h with h | h <;> simp [Prod.eq_iff_fst_eq_snd_eq] at h <;>
        simp [ha, hb, hc, h] <;> (split_ands <;> decide)
