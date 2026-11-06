import Mathlib
/- Let $k$ and $m$ be coprime positive integers. Suppose $a$ and $b$ are natural numbers (where $b \neq 0$) such that the numbers $a x + k$ and $b x + m$ are not coprime for any natural number $x$ (meaning $x \in \{0, 1, 2, \dots\}$). Show that the integer part of the quotient $a/b$ is equal to $\lfloor m/k \rfloor$. (This means `Nat.div a b = Nat.div m k`). -/
theorem algebra_640988 (k m a b : ℕ) (hk : k > 0) (hm : m > 0) (hb : b ≠ 0) (h : ∀ x : ℕ, x > 0 → Nat.gcd (a * x + k) (b * x + m) ≠ 1) (h1 : Nat.Coprime k m): a / b = k / m:= by
  -- First, prove that a ≠ 0 by contradiction
  have ha : a ≠ 0:= by
    by_contra H
    subst a
    simp at h
    specialize h k (by omega)
    absurd h
    replace h1 : Nat.gcd k m = 1:= by exact h1
    exact (Nat.coprime_mul_right_add_right k m b).mpr h1

  -- Prove that b * k = a * m by contradiction
  have h2 : b * k = a * m:= by
    by_contra H
    replace H : b * k < a * m ∨ b * k > a * m:= by omega
    rcases H with H | H
    .
      -- Case 1: b * k < a * m
      set t:= a * m - b * k with ht
      clear_value t
      replace H : t > 0:= by omega
      specialize h t H
      set d:= Nat.gcd (a * t + k) (b * t + m) with hd
      clear_value d
      -- Show that d divides a * t + k
      have g1 : d ∣ a * t + k:= by
        subst d
        exact Nat.gcd_dvd_left (a * t + k) (b * t + m)
      -- Show that d divides b * t + m
      have g2 : d ∣ b * t + m:= by
        subst d
        exact Nat.gcd_dvd_right (a * t + k) (b * t + m)
      -- Show that d divides t
      have g : d ∣ t:= by
        replace g1 : d ∣ b * (a * t + k):= by exact Dvd.dvd.mul_left g1 b
        replace g2 : d ∣ a * (b * t + m):= by exact Dvd.dvd.mul_left g2 a
        rw [show a * (b * t + m) = a * b * t + a * m by ring] at g2
        replace ht : t + b * k = a * m:= by omega
        rw [←ht] at g2
        rw [show a * b * t + (t + b * k) = b * (a * t + k) + t by ring] at g2
        exact (Nat.dvd_add_iff_right g1).mpr g2
      -- Show that d divides a * t and b * t
      have g3 : d ∣ a * t:= by exact Dvd.dvd.mul_left g a
      have g4 : d ∣ b * t:= by exact Dvd.dvd.mul_left g b
      -- Show that d divides k and m
      replace g1 : d ∣ k:= by exact (Nat.dvd_add_iff_right g3).mpr g1
      replace g2 : d ∣ m:= by exact (Nat.dvd_add_iff_right g4).mpr g2
      -- Since d divides both k and m, and k and m are coprime, d must be 1
      replace g1 : d ∣ Nat.gcd k m:= by exact Nat.dvd_gcd g1 g2
      rw [h1] at g1
      simp at g1
      omega
    .
      -- Case 2: b * k > a * m
      set t:= b * k - a * m with ht
      clear_value t
      replace H : t > 0:= by omega
      specialize h t H
      set d:= Nat.gcd (a * t + k) (b * t + m) with hd
      clear_value d
      -- Show that d divides a * t + k
      have g1 : d ∣ a * t + k:= by
        subst d
        exact Nat.gcd_dvd_left (a * t + k) (b * t + m)
      -- Show that d divides b * t + m
      have g2 : d ∣ b * t + m:= by
        subst d
        exact Nat.gcd_dvd_right (a * t + k) (b * t + m)
      -- Show that d divides t
      have g : d ∣ t:= by
        replace g1 : d ∣ b * (a * t + k):= by exact Dvd.dvd.mul_left g1 b
        replace g2 : d ∣ a * (b * t + m):= by exact Dvd.dvd.mul_left g2 a
        rw [show b * (a * t + k) = b * a * t + b * k by ring] at g1
        replace ht : t + a * m = b * k:= by omega
        rw [←ht] at g1
        rw [show b * a * t + (t + a * m) = a * (b * t + m) + t by ring] at g1
        exact (Nat.dvd_add_iff_right g2).mpr g1
      -- Show that d divides a * t and b * t
      have g3 : d ∣ a * t:= by exact Dvd.dvd.mul_left g a
      have g4 : d ∣ b * t:= by exact Dvd.dvd.mul_left g b
      -- Show that d divides k and m
      replace g1 : d ∣ k:= by exact (Nat.dvd_add_iff_right g3).mpr g1
      replace g2 : d ∣ m:= by exact (Nat.dvd_add_iff_right g4).mpr g2
      -- Since d divides both k and m, and k and m are coprime, d must be 1
      replace g1 : d ∣ Nat.gcd k m:= by exact Nat.dvd_gcd g1 g2
      rw [h1] at g1
      simp at g1
      omega

  -- Convert to real numbers and show a/b = k/m
  rify at h2
  replace h2 : (↑a : ℝ) / b = k / m:= by field_simp ; linarith

  -- Prove that floor(a/b) = a/b as natural numbers
  have g1 : ⌊(↑a : ℝ) / b⌋ = (a / b : ℕ):= by
    -- Use division algorithm: a = b * (a/b) + (a%b)
    have g1 : a = b * (a / b) + a % b:= by exact Eq.symm (Nat.div_add_mod a b)
    set r:= a % b with hr
    set k:= a / b with hk
    clear_value k r
    -- Show that remainder r < b
    replace hr : r < b:= by subst r ; refine Nat.mod_lt a (by omega)
    -- Express a/b as k + r/b
    replace g1 : (↑a : ℝ) / b = k + r / b:= by
      field_simp
      rify at g1
      linarith
    -- Show that r/b is non-negative and less than 1
    have g2 : (↑r : ℝ) / b ≥ 0:= by positivity
    have g3 : (↑r : ℝ) / b < 1:= by
      rify at hr
      replace hb : b > 0:= by omega
      rify at hb
      exact Bound.div_lt_one_of_pos_of_lt hb hr
    -- Use floor definition to conclude
    refine Int.floor_eq_iff.mpr ?_
    simp
    refine ⟨by linarith, by linarith⟩

  -- Prove that floor(k/m) = k/m as natural numbers
  have g2 : ⌊(↑k : ℝ) / m⌋ = (k / m : ℕ):= by
    -- Use division algorithm: k = m * (k/m) + (k%m)
    have g2 : k = m * (k / m) + k % m:= by exact Eq.symm (Nat.div_add_mod k m)
    set r:= k % m with hr
    set s:= k / m with hk
    clear_value s r
    -- Show that remainder r < m
    replace hr : r < m:= by subst r ; refine Nat.mod_lt k (by omega)
    -- Express k/m as s + r/m
    replace g2 : (↑k : ℝ) / m = s + r / m:= by
      field_simp
      rify at g2
      linarith
    -- Show that r/m is non-negative and less than 1
    have g3 : (↑r : ℝ) / m ≥ 0:= by positivity
    have g4 : (↑r : ℝ) / m < 1:= by
      rify at hr
      replace hm : m > 0:= by omega
      rify at hm
      exact Bound.div_lt_one_of_pos_of_lt hm hr
    -- Use floor definition to conclude
    refine Int.floor_eq_iff.mpr ?_
    simp
    refine ⟨by linarith, by linarith⟩

  -- Final step: combine all results to prove a/b = k/m
  rify
  simp at g1 g2
  rw [←g1, h2, ←g2]
