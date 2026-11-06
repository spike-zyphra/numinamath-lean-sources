import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Show that if the difference of two positive cube numbers is a positive prime,
    then this prime number has remainder  $1$  after division by  $6$ .-/
theorem number_theory_8631
  (p : ℕ)
  (h₀ : ∃ n m : ℕ, n > 0 ∧ m > 0 ∧ p = n^3 - m^3 ∧ Nat.Prime p) :
  p % 6 = 1 := by
    obtain ⟨a, b, ha, hb, c1, hp⟩ := h₀
    -- Because $p$ is positive, $b < a$.
    have h1 : b < a := by
      have : 0 < p := Prime.pos hp
      have := c1 ▸ this
      have : b^3 < a^3 := Nat.lt_of_sub_pos this
      exact lt_of_pow_lt_pow_left' 3 this
    have c2 : (a - b) * (a^2 + a*b + b^2) = a^3 - b^3 := by
      zify
      rw [Nat.cast_sub (le_of_lt h1), Nat.cast_sub ]
      simp
      ring_nf
      refine Nat.pow_le_pow_of_le_left (le_of_lt h1) 3
    -- Because $a^3-b^3=p$, we have
    -- \[(a-b)(a^2+ab+b^2)=p.\]
    replace c2 := c2.trans c1.symm
    have h2 := Nat.prime_mul_iff.1 (c2 ▸ hp)
    -- We have two cases: Case1 : $a-b=p$  and  $a^2+ab+b^2=1$ or
    -- Case2 : $a-b=1$  and  $a^2+ab+b^2=p$.
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · -- Case 1 is impossible.
      have : 2 ≤ a := by
        have : 2 ≤ a - b := Prime.two_le h3
        linarith
      nlinarith
    · -- Hence  $a=b+1$ . Substitute back,
      -- \begin{align*}
      -- &(b+1)^2+(b+1)b+b^2=p
      -- &3b(b+1)+1=p
      -- \end{align*}
      have c3 : a = b + 1 := (Nat.sub_eq_iff_eq_add' (le_of_lt h1)).mp h4
      rw [h4, c3] at c2
      simp at c2
      -- Note that  $2\mid b(b+1)$ , hence  $6\mid 3b(b+1)$ . Therefore
      -- \[
      -- p=3b(b+1)+1\equiv 1\pmod{6}
      -- \]
      -- as expected.
      have aux (n : ℕ) : 2 ∣ n * (n + 1) := by
        by_cases h : n % 2 = 0
        · replace h :=  Nat.dvd_of_mod_eq_zero h
          exact Dvd.dvd.mul_right h (n + 1)
        · have : n % 2 < 2 := Nat.mod_lt n (by linarith)
          have h : n % 2 = 1 := by simp at *; linarith
          have : (n + 1) % 2 = 0 := by rw [Nat.add_mod]; simp [h]
          have := Nat.dvd_of_mod_eq_zero this
          exact Dvd.dvd.mul_left this n
      have c4 : 3 * b * (b + 1) + 1 = p := by linarith
      have : 2 * 3 ∣ 3 * b * (b + 1) := by
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide)
          (by rw [mul_assoc]; exact dvd_mul_of_dvd_right (aux b) 3) (by simp [mul_assoc])
      rw [←c4]
      nth_rw 3 [show 1 = 1 % 6 by simp]
      rw [←Nat.ModEq]
      refine
        ModEq.symm
          ((fun {n a b} h ↦ (modEq_iff_dvd' h).mpr) (by nlinarith) this)
