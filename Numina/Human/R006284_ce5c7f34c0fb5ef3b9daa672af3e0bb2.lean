import Mathlib

/-Let k be a positive integer. Determine the residue of
9^10k modulo 17. Show that this residue is
13 if k≡1(mod4), 16 if k≡2(mod4),
4 if k≡3(mod4), and 1 if k≡0(mod4).-/

theorem number_theory_635521 (k c: ℕ) (h: c = 9):
  (k % 4 = 0 ∧ c ^ (10 * k) % 17 = 1) ∨ (k % 4 = 1 ∧ c ^ (10 * k) % 17 = 13) ∨
  (k % 4 = 2 ∧ c ^ (10 * k) % 17 = 16) ∨ (k % 4 = 3 ∧ c ^ (10 * k) % 17 = 4) := by

  have hc: c ^ 10 % 17 = 13 := by
    simp [h]
  clear h

  -- we show that the function is 4-periodic
  have p: ∀ n, c ^ (10 * (n + 4)) % 17 = c ^ (10 * n) % 17 := by
    intro n
    induction' n with n ih
    .
      simp
      rw [show c ^ 40 = (c ^ 10) ^ 4 by ring]
      rw [Nat.pow_mod]
      rw [hc]

    .
      have s1: c ^ (10 * (n + 1 + 4)) = c ^ (10 * (n + 4)) * c ^ 10 := by
        rw [show 10 * (n + 1 + 4) = 10 * (n + 4) + 10 by omega]
        rw [Nat.pow_add]
      rw [s1]
      clear s1
      rw [Nat.mul_mod]
      clear ih
      have s2: c ^ (10 * (n + 4)) = c ^ (10 * (n + 1)) * c ^ 30 := by
        rw [show 10 * (n + 4) = 10 * (n + 1) + 30 by omega]
        rw [Nat.pow_add]
      rw [s2]
      clear s2
      set a:= c ^ (10 * (n + 1))
      set b:= c ^ 30
      set g:= c ^ 10
      rw [← Nat.mul_mod]
      rw [show a * b * g = a * (b * g) by ring]
      rw [Nat.mul_mod]
      suffices b * g % 17 = 1 by
        rw [this]
        simp
      simp [b, g]
      rw [show c ^ 30 * c ^ 10 = (c ^ 10) ^ 4 by ring]
      simp [g] at hc
      rw [Nat.pow_mod]
      rw [hc]

  -- then we can use the periodicity to show the result
  have f: ∀ n, n % 4 = 0 → c ^ (10 * n) % 17 = 1 := by
    intro n hn
    set x:= n / 4
    set y:= n % 4
    have s: n = 4 * x + y := by
      omega
    rw [show 10 * n = 10 * (4 * x + y) by omega]
    rw [Nat.mul_add]
    simp [hn]
    induction' x with x ih
    .
      simp
    .
      rw [show 10 * (4 * (x + 1)) = 10 * (4 * x) + 40 by omega]
      ring_nf
      rw [Nat.mul_mod]
      ring_nf at ih
      rw [ih]
      rw [show c ^ 40 = (c ^ 10) ^ 4 by ring]
      simp
      rw [Nat.pow_mod]
      rw [hc]
      simp

  have r: k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
     omega
  set x:= k / 4
  set y:= k % 4
  have s: k = 4 * x + y := by
    omega
  rcases r with r | r | r | r

  -- case k % 4 = 0
  .
    left
    simp [r]
    simp [s, r]
    specialize f (4 * x) (by simp)
    tauto

  -- case k % 4 = 1
  .
    right
    left
    simp [r]
    simp [s, r]
    rw [show 10 * (4 * x + 1) = 10 * (4 * x) + 10 by omega]
    ring_nf
    rw [Nat.mul_mod]
    rw [hc]
    specialize f (x * 4) (by simp)
    ring_nf at f
    rw [f]
    simp

  -- case k % 4 = 2
  .
    right
    right
    left
    simp [r]
    simp [s, r]
    rw [show 10 * (4 * x + 2) = 10 * (4 * x) + 20 by omega]
    ring_nf
    rw [Nat.mul_mod]
    rw [show c ^ 20 = (c ^ 10) ^ 2 by ring]
    have s: (c ^ 10) ^ 2 % 17 = 16 := by
      rw [Nat.pow_mod]
      rw [hc]
    rw [s]
    specialize f (x * 4) (by simp)
    ring_nf at f
    rw [f]
    simp

  -- case k % 4 = 3
  .
    right
    right
    right
    simp [r]
    simp [s, r]
    rw [show 10 * (4 * x + 3) = 10 * (4 * x) + 30 by omega]
    ring_nf
    rw [Nat.mul_mod]
    rw [show c ^ 30 = (c ^ 10) ^ 3 by ring]
    have s: (c ^ 10) ^ 3 % 17 = 4 := by
      rw [Nat.pow_mod]
      rw [hc]
    rw [s]
    specialize f (x * 4) (by simp)
    ring_nf at f
    rw [f]
    simp
